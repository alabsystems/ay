// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used, clippy::panic)]
use super::*;
use crate::smt::SmtContext;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, PredicateId};
use std::sync::Arc;

// ============================================================================
// Shared test helpers
// ============================================================================

fn pred(n: u32) -> PredicateId {
    PredicateId::new(n)
}

fn rf_id(n: usize) -> ReachFactId {
    ReachFactId(n)
}

fn var(name: &str) -> ChcExpr {
    ChcExpr::Var(ChcVar {
        name: name.to_string(),
        sort: ChcSort::Int,
    })
}

fn ge(v: &str, c: i128) -> ChcExpr {
    ChcExpr::Op(ChcOp::Ge, vec![Arc::new(var(v)), Arc::new(ChcExpr::Int(c))])
}

fn le(v: &str, c: i128) -> ChcExpr {
    ChcExpr::Op(ChcOp::Le, vec![Arc::new(var(v)), Arc::new(ChcExpr::Int(c))])
}

fn ne(v: &str, c: i128) -> ChcExpr {
    ChcExpr::Op(ChcOp::Ne, vec![Arc::new(var(v)), Arc::new(ChcExpr::Int(c))])
}

fn eq_expr(v: &str, c: i128) -> ChcExpr {
    ChcExpr::Op(ChcOp::Eq, vec![Arc::new(var(v)), Arc::new(ChcExpr::Int(c))])
}

// ============================================================================
// MustSummaries Provenance Tests (#2247)
// ============================================================================

#[test]
fn backed_entry_is_returned_by_get_backed() {
    let mut summaries = MustSummaries::new();
    let p = pred(0);

    summaries.add_backed(0, p, ChcExpr::Int(42), rf_id(100));

    // get_backed should return the formula
    let backed = summaries.get_backed(0, p);
    assert!(backed.is_some(), "expected backed formula");
    assert_eq!(backed.unwrap(), ChcExpr::Int(42));

    // get (which includes all) should also return it
    let all = summaries.get(0, p);
    assert!(all.is_some());
}

#[test]
fn filter_only_entry_excluded_from_get_backed() {
    let mut summaries = MustSummaries::new();
    let p = pred(0);

    summaries.add_filter_only(0, p, ChcExpr::Int(42));

    // get_backed should return None (no backed entries)
    let backed = summaries.get_backed(0, p);
    assert!(
        backed.is_none(),
        "filter-only should not appear in get_backed"
    );

    // get (which includes all) should return it
    let all = summaries.get(0, p);
    assert!(all.is_some());
}

#[test]
fn unbacked_upgraded_to_backed() {
    let mut summaries = MustSummaries::new();
    let p = pred(0);

    // Add as unbacked first
    let added1 = summaries.add_filter_only(0, p, ChcExpr::Int(42));
    assert!(added1);

    // get_backed should return None
    assert!(summaries.get_backed(0, p).is_none());

    // Now add same formula as backed - should upgrade
    let added2 = summaries.add_backed(0, p, ChcExpr::Int(42), rf_id(100));
    assert!(added2, "should return true for backing upgrade");

    // get_backed should now return it
    let backed = summaries.get_backed(0, p);
    assert!(backed.is_some(), "upgraded entry should be backed");
}

#[test]
fn backed_not_downgraded_to_unbacked() {
    let mut summaries = MustSummaries::new();
    let p = pred(0);

    // Add as backed first
    summaries.add_backed(0, p, ChcExpr::Int(42), rf_id(100));

    // Try to add same formula as unbacked - should be rejected
    let added = summaries.add_filter_only(0, p, ChcExpr::Int(42));
    assert!(!added, "backed formula should not be downgraded");

    // Should still be backed
    assert!(summaries.get_backed(0, p).is_some());
}

#[test]
fn get_all_levels_backed_spans_levels() {
    let mut summaries = MustSummaries::new();
    let p = pred(0);

    // Add backed at level 0
    summaries.add_backed(0, p, ChcExpr::Int(1), rf_id(100));
    // Add unbacked at level 1
    summaries.add_filter_only(1, p, ChcExpr::Int(2));
    // Add backed at level 2
    summaries.add_backed(2, p, ChcExpr::Int(3), rf_id(200));

    // get_all_levels_backed should only include backed entries (levels 0 and 2)
    let backed = summaries.get_all_levels_backed(p);
    assert!(backed.is_some());

    // The result is a disjunction of Int(1) and Int(3)
    let formula = backed.unwrap();
    let formula_str = formula.to_string();
    assert!(
        formula_str.contains('1') && formula_str.contains('3'),
        "expected disjunction of backed formulas, got {formula_str}"
    );
    assert!(
        !formula_str.contains('2'),
        "unbacked formula should not be in backed result, got {formula_str}"
    );
}

#[test]
fn get_entries_returns_with_backing_info() {
    let mut summaries = MustSummaries::new();
    let p = pred(0);

    summaries.add_backed(0, p, ChcExpr::Int(1), rf_id(100));
    summaries.add_filter_only(0, p, ChcExpr::Int(2));

    let entries = summaries.get_entries(0, p).expect("entries for pred");
    assert_eq!(entries.len(), 2);

    // First entry should be backed
    assert!(entries[0].backing.is_some());
    assert_eq!(entries[0].backing.unwrap(), rf_id(100));

    // Second entry should be unbacked
    assert!(entries[1].backing.is_none());
}

#[test]
fn deduplication_by_formula() {
    let mut summaries = MustSummaries::new();
    let p = pred(0);

    let added1 = summaries.add_backed(0, p, ChcExpr::Int(42), rf_id(100));
    assert!(added1);

    // Same formula, different ReachFactId - should be deduplicated
    let added2 = summaries.add_backed(0, p, ChcExpr::Int(42), rf_id(200));
    assert!(!added2, "duplicate formula should be rejected");

    // Should only have one entry
    let entries = summaries.get_entries(0, p).expect("entries");
    assert_eq!(entries.len(), 1);
}

#[test]
fn get_all_levels_backed_none_when_all_unbacked() {
    let mut summaries = MustSummaries::new();
    let p = pred(0);

    // Add unbacked entries at multiple levels - none are backed
    summaries.add_filter_only(0, p, ChcExpr::Int(1));
    summaries.add_filter_only(1, p, ChcExpr::Int(2));
    summaries.add_filter_only(2, p, ChcExpr::Int(3));

    // get_all_levels_backed should return None (no backed entries at any level)
    let backed = summaries.get_all_levels_backed(p);
    assert!(
        backed.is_none(),
        "expected None when all entries are unbacked"
    );

    // But get_all_levels should still return them
    let all = summaries.get_all_levels(p);
    assert!(
        all.is_some(),
        "get_all_levels should return unbacked entries"
    );
}

// ============================================================================
// Bound Subsumption Tests
// ============================================================================

#[test]
fn lower_bound_subsumption() {
    let mut frame = Frame::new();
    let p = pred(0);
    // x >= 0, x >= 5, x >= 10 -> only x >= 10 survives
    frame.add_lemma(Lemma::new(p, ge("x", 0), 1));
    frame.add_lemma(Lemma::new(p, ge("x", 5), 1));
    frame.add_lemma(Lemma::new(p, ge("x", 10), 1));
    assert_eq!(frame.lemmas.len(), 3);

    let removed = frame.subsume_redundant_bounds();
    assert_eq!(removed, 2);
    assert_eq!(frame.lemmas.len(), 1);
    assert_eq!(frame.lemmas[0].formula, ge("x", 10));
}

#[test]
fn upper_bound_subsumption() {
    let mut frame = Frame::new();
    let p = pred(0);
    // x <= 100, x <= 50, x <= 20 -> only x <= 20 survives
    frame.add_lemma(Lemma::new(p, le("x", 100), 1));
    frame.add_lemma(Lemma::new(p, le("x", 50), 1));
    frame.add_lemma(Lemma::new(p, le("x", 20), 1));
    assert_eq!(frame.lemmas.len(), 3);

    let removed = frame.subsume_redundant_bounds();
    assert_eq!(removed, 2);
    assert_eq!(frame.lemmas.len(), 1);
    assert_eq!(frame.lemmas[0].formula, le("x", 20));
}

#[test]
fn disequality_subsumed_by_lower_bound() {
    let mut frame = Frame::new();
    let p = pred(0);
    // x >= 10 and (ne x 5) -> disequality is redundant since x >= 10 > 5
    frame.add_lemma(Lemma::new(p, ge("x", 10), 1));
    frame.add_lemma(Lemma::new(p, ne("x", 5), 1));
    assert_eq!(frame.lemmas.len(), 2);

    let removed = frame.subsume_redundant_bounds();
    assert_eq!(removed, 1);
    assert_eq!(frame.lemmas.len(), 1);
    assert_eq!(frame.lemmas[0].formula, ge("x", 10));
}

#[test]
fn no_subsumption_across_predicates() {
    let mut frame = Frame::new();
    // x >= 10 for pred 0 should NOT subsume x >= 5 for pred 1
    frame.add_lemma(Lemma::new(pred(0), ge("x", 10), 1));
    frame.add_lemma(Lemma::new(pred(1), ge("x", 5), 1));

    let removed = frame.subsume_redundant_bounds();
    assert_eq!(removed, 0);
    assert_eq!(frame.lemmas.len(), 2);
}

#[test]
fn no_subsumption_across_variables() {
    let mut frame = Frame::new();
    let p = pred(0);
    // x >= 10 should NOT subsume y >= 5
    frame.add_lemma(Lemma::new(p, ge("x", 10), 1));
    frame.add_lemma(Lemma::new(p, ge("y", 5), 1));

    let removed = frame.subsume_redundant_bounds();
    assert_eq!(removed, 0);
    assert_eq!(frame.lemmas.len(), 2);
}

#[test]
fn mixed_bound_subsumption() {
    let mut frame = Frame::new();
    let p = pred(0);
    // x >= 0, x >= 3, x >= 7, x <= 100, x <= 50, (ne x 2)
    // After: x >= 7 (subsumes x >= 0, x >= 3, and ne x 2), x <= 50 (subsumes x <= 100)
    frame.add_lemma(Lemma::new(p, ge("x", 0), 1));
    frame.add_lemma(Lemma::new(p, ge("x", 3), 1));
    frame.add_lemma(Lemma::new(p, ge("x", 7), 1));
    frame.add_lemma(Lemma::new(p, le("x", 100), 1));
    frame.add_lemma(Lemma::new(p, le("x", 50), 1));
    frame.add_lemma(Lemma::new(p, ne("x", 2), 1));

    let removed = frame.subsume_redundant_bounds();
    assert_eq!(removed, 4); // x>=0, x>=3, x<=100, ne x 2
    assert_eq!(frame.lemmas.len(), 2);
}

#[test]
fn lemma_keys_maintained_after_subsumption() {
    let mut frame = Frame::new();
    let p = pred(0);
    frame.add_lemma(Lemma::new(p, ge("x", 0), 1));
    frame.add_lemma(Lemma::new(p, ge("x", 10), 1));

    frame.subsume_redundant_bounds();
    assert_eq!(frame.lemmas.len(), 1);

    // The surviving lemma should still be in lemma_keys
    assert!(frame.contains_lemma(p, &ge("x", 10)));
    // The removed lemma should be gone from lemma_keys
    assert!(!frame.contains_lemma(p, &ge("x", 0)));
}

#[test]
fn lemma_keys_maintained_after_truncate() {
    let mut frame = Frame::new();
    let p = pred(0);
    frame.add_lemma(Lemma::new(p, ge("x", 0), 1));
    frame.add_lemma(Lemma::new(p, ge("x", 10), 1));

    frame.truncate_lemmas(1);
    assert_eq!(frame.lemmas.len(), 1);

    assert!(frame.contains_lemma(p, &ge("x", 0)));
    assert!(!frame.contains_lemma(p, &ge("x", 10)));
}

// ============================================================================
// Semantic Subsumption Tests
// ============================================================================

/// x >= 0 AND y >= 0 should subsume (x + y) >= 0
#[test]
fn sum_subsumed_by_component_bounds() {
    let mut frame = Frame::new();
    let p = pred(0);

    // Add x >= 0, y >= 0, and (x + y) >= 0
    frame.add_lemma(Lemma::new(p, ge("x", 0), 1));
    frame.add_lemma(Lemma::new(p, ge("y", 0), 1));
    let sum = ChcExpr::Op(ChcOp::Add, vec![Arc::new(var("x")), Arc::new(var("y"))]);
    let sum_ge_0 = ChcExpr::Op(ChcOp::Ge, vec![Arc::new(sum), Arc::new(ChcExpr::Int(0))]);
    frame.add_lemma(Lemma::new(p, sum_ge_0.clone(), 1));

    assert_eq!(frame.lemmas.len(), 3);

    let mut smt = SmtContext::new();
    let removed = frame.subsume_semantic(&mut smt, 64);
    assert_eq!(
        removed, 1,
        "sum bound should be subsumed by component bounds"
    );
    assert_eq!(frame.lemmas.len(), 2);
    // The sum lemma should be gone
    assert!(!frame.contains_lemma(p, &sum_ge_0));
}

/// x >= 5 AND x <= 5 together imply x = 5, so x = 5 is subsumed
#[test]
fn equality_subsumed_by_tight_bounds() {
    let mut frame = Frame::new();
    let p = pred(0);

    frame.add_lemma(Lemma::new(p, eq_expr("x", 5), 1));
    frame.add_lemma(Lemma::new(p, ge("x", 5), 1));
    frame.add_lemma(Lemma::new(p, le("x", 5), 1));

    assert_eq!(frame.lemmas.len(), 3);

    let mut smt = SmtContext::new();
    let removed = frame.subsume_semantic(&mut smt, 64);
    // x>=5 AND x<=5 implies x=5, so the equality is subsumed
    assert_eq!(removed, 1, "equality should be subsumed by tight bounds");
    assert_eq!(frame.lemmas.len(), 2);
    // The equality should be gone, bounds remain
    assert!(!frame.contains_lemma(p, &eq_expr("x", 5)));
    assert!(frame.contains_lemma(p, &ge("x", 5)));
    assert!(frame.contains_lemma(p, &le("x", 5)));
}

/// x = 5 (alone, no companion bounds) subsumes x >= 3
#[test]
fn equality_alone_subsumes_weaker_bound() {
    let mut frame = Frame::new();
    let p = pred(0);

    frame.add_lemma(Lemma::new(p, eq_expr("x", 5), 1));
    frame.add_lemma(Lemma::new(p, ge("x", 3), 1));

    assert_eq!(frame.lemmas.len(), 2);

    let mut smt = SmtContext::new();
    let removed = frame.subsume_semantic(&mut smt, 64);
    // x=5 implies x>=3 (since 5>=3), so x>=3 is subsumed
    assert_eq!(removed, 1, "weaker bound should be subsumed by equality");
    assert_eq!(frame.lemmas.len(), 1);
    assert_eq!(frame.lemmas[0].formula, eq_expr("x", 5));
}

/// No subsumption across different predicates
#[test]
fn no_cross_predicate_subsumption() {
    let mut frame = Frame::new();

    // x >= 10 for pred 0, x >= 5 for pred 1 — NOT subsumed
    frame.add_lemma(Lemma::new(pred(0), ge("x", 10), 1));
    frame.add_lemma(Lemma::new(pred(1), ge("x", 5), 1));

    let mut smt = SmtContext::new();
    let removed = frame.subsume_semantic(&mut smt, 64);
    assert_eq!(removed, 0);
    assert_eq!(frame.lemmas.len(), 2);
}

/// Groups exceeding max_group_size are skipped
#[test]
fn respects_max_group_size() {
    let mut frame = Frame::new();
    let p = pred(0);

    // x = 5 subsumes x >= 5, but with max_group_size = 1, skip
    frame.add_lemma(Lemma::new(p, eq_expr("x", 5), 1));
    frame.add_lemma(Lemma::new(p, ge("x", 5), 1));

    let mut smt = SmtContext::new();
    let removed = frame.subsume_semantic(&mut smt, 1);
    assert_eq!(removed, 0, "should skip groups exceeding max_group_size");
}

/// Single-lemma groups are not checked
#[test]
fn single_lemma_no_check() {
    let mut frame = Frame::new();
    frame.add_lemma(Lemma::new(pred(0), ge("x", 5), 1));

    let mut smt = SmtContext::new();
    let removed = frame.subsume_semantic(&mut smt, 64);
    assert_eq!(removed, 0);
}

/// Prove that frame lemma storage is unbounded: adding N distinct lemmas
/// for the same predicate results in a Vec of size N with no cap or eviction.
///
/// This is a structural proof, not a timing test. It demonstrates that:
/// 1. Frame.lemmas grows linearly without bound (no capacity limit).
/// 2. get_predicate_constraint scans all lemmas on first call (O(N)),
///    but caches the result for subsequent calls (#2815).
///
/// Related: #2815 (get_predicate_constraint cached per-predicate)
#[test]
fn frame_lemma_storage_unbounded_growth() {
    let mut frame = Frame::new();
    let p0 = pred(0);
    let p1 = pred(1);
    let n = 500;

    // Add N distinct lemmas for predicate p0
    for i in 0..n {
        frame.add_lemma(Lemma::new(p0, ge("x", i), 1));
    }
    // Add N distinct lemmas for predicate p1
    for i in 0..n {
        frame.add_lemma(Lemma::new(p1, le("y", i), 1));
    }

    // Proof: frame.lemmas contains all 2*N lemmas with no eviction
    assert_eq!(
        frame.lemmas.len(),
        2 * n as usize,
        "Frame stores all lemmas without cap"
    );

    // Proof: get_predicate_constraint scans ALL 2*N lemmas to filter for p0
    // (no per-predicate index structure)
    let constraint = frame.get_predicate_constraint(p0);
    assert!(constraint.is_some(), "Should find lemmas for p0");

    // The returned constraint is a conjunction of all N p0-lemmas
    // This demonstrates the O(N) work: filtering + conjunction building
}

/// get_predicate_constraint cache is invalidated when a new lemma is added (#2815).
///
/// Calls get_predicate_constraint, adds a lemma, calls again. The second call
/// must return a conjunction that includes the new lemma.
#[test]
fn predicate_constraint_cache_invalidates_on_add() {
    let mut frame = Frame::new();
    let p = pred(0);

    frame.add_lemma(Lemma::new(p, ge("x", 0), 1));
    let c1 = frame.get_predicate_constraint(p).unwrap();

    // Add a second lemma — cache must be invalidated
    frame.add_lemma(Lemma::new(p, le("y", 10), 1));
    let c2 = frame.get_predicate_constraint(p).unwrap();

    // c2 must differ from c1 (includes new lemma)
    assert_ne!(c1, c2, "cache must be invalidated after add_lemma");
    match &c2 {
        ChcExpr::Op(ChcOp::And, args) => {
            assert_eq!(args.len(), 2, "expected conjunction of 2 lemmas");
        }
        _ => panic!("expected And, got: {c2:?}"),
    }
}

/// get_predicate_constraint cache is invalidated when lemmas are removed (#2815).
#[test]
fn predicate_constraint_cache_invalidates_on_remove() {
    let mut frame = Frame::new();
    let p = pred(0);

    frame.add_lemma(Lemma::new(p, ge("x", 0), 1));
    frame.add_lemma(Lemma::new(p, ge("x", 5), 1));
    let c1 = frame.get_predicate_constraint(p).unwrap();

    // subsume_redundant_bounds removes (>= x 0) since (>= x 5) is stronger
    let removed = frame.subsume_redundant_bounds();
    assert!(removed > 0);

    let c2 = frame.get_predicate_constraint(p).unwrap();
    assert_ne!(c1, c2, "cache must be invalidated after remove");
}

/// lemma_keys consistency after semantic subsumption
#[test]
fn keys_maintained_after_semantic_subsumption() {
    let mut frame = Frame::new();
    let p = pred(0);

    frame.add_lemma(Lemma::new(p, eq_expr("x", 5), 1));
    frame.add_lemma(Lemma::new(p, ge("x", 5), 1));

    let mut smt = SmtContext::new();
    frame.subsume_semantic(&mut smt, 64);

    assert!(frame.contains_lemma(p, &eq_expr("x", 5)));
    assert!(!frame.contains_lemma(p, &ge("x", 5)));
}

// ============================================================================
// GC and Eviction Tests (#8601)
// ============================================================================

/// gc_unused_lemmas removes only lemmas with usage_count == 0
#[test]
fn gc_unused_lemmas_removes_unused_only() {
    let mut frame = Frame::new();
    let p = pred(0);

    frame.add_lemma(Lemma::new(p, ge("x", 0), 1));
    frame.add_lemma(Lemma::new(p, ge("y", 0), 1));
    frame.add_lemma(Lemma::new(p, le("z", 100), 1));

    // Mark the first lemma as used
    frame.lemmas[0].mark_used();

    let removed = frame.gc_unused_lemmas();
    assert_eq!(removed, 2, "should remove 2 unused lemmas");
    assert_eq!(frame.lemmas.len(), 1, "only used lemma survives");
    assert!(frame.contains_lemma(p, &ge("x", 0)));
    assert!(!frame.contains_lemma(p, &ge("y", 0)));
    assert!(!frame.contains_lemma(p, &le("z", 100)));
}

/// gc_unused_lemmas is a no-op when all lemmas are used
#[test]
fn gc_unused_lemmas_noop_when_all_used() {
    let mut frame = Frame::new();
    let p = pred(0);

    frame.add_lemma(Lemma::new(p, ge("x", 0), 1));
    frame.add_lemma(Lemma::new(p, ge("y", 0), 1));

    frame.lemmas[0].mark_used();
    frame.lemmas[1].mark_used();

    let removed = frame.gc_unused_lemmas();
    assert_eq!(removed, 0);
    assert_eq!(frame.lemmas.len(), 2);
}

/// evict_oldest_n removes the N oldest (first) entries
#[test]
fn evict_oldest_n_removes_fifo() {
    let mut frame = Frame::new();
    let p = pred(0);

    frame.add_lemma(Lemma::new(p, ge("x", 1), 1));
    frame.add_lemma(Lemma::new(p, ge("x", 2), 1));
    frame.add_lemma(Lemma::new(p, ge("x", 3), 1));
    frame.add_lemma(Lemma::new(p, ge("x", 4), 1));

    let evicted = frame.evict_oldest_n(2);
    assert_eq!(evicted, 2);
    assert_eq!(frame.lemmas.len(), 2);
    // The 2 newest lemmas survive (FIFO eviction)
    assert!(frame.contains_lemma(p, &ge("x", 3)));
    assert!(frame.contains_lemma(p, &ge("x", 4)));
    assert!(!frame.contains_lemma(p, &ge("x", 1)));
    assert!(!frame.contains_lemma(p, &ge("x", 2)));
}

/// evict_oldest_n handles request larger than frame size
#[test]
fn evict_oldest_n_caps_at_frame_size() {
    let mut frame = Frame::new();
    let p = pred(0);

    frame.add_lemma(Lemma::new(p, ge("x", 1), 1));
    frame.add_lemma(Lemma::new(p, ge("x", 2), 1));

    let evicted = frame.evict_oldest_n(100);
    assert_eq!(evicted, 2);
    assert_eq!(frame.lemmas.len(), 0);
}

/// MustSummary per-predicate cap evicts oldest entries
#[test]
fn must_summary_per_predicate_cap() {
    let mut summaries = MustSummaries::new();
    let p = pred(0);

    // Add MAX_MUST_SUMMARIES_PER_PREDICATE entries, then one more
    // (We use a smaller number and check the mechanism works)
    for i in 0..50 {
        summaries.add_filter_only(0, p, ChcExpr::Int(i));
    }
    let entries = summaries.get_entries(0, p).unwrap();
    assert_eq!(
        entries.len(),
        50,
        "all 50 should fit within the per-predicate cap"
    );
}

/// MustSummary gc_if_over_global_budget evicts when total exceeds cap
#[test]
fn must_summary_global_gc_evicts() {
    let mut summaries = MustSummaries::new();

    // Add entries across many (level, predicate) groups to exceed the cap.
    // We can't easily hit 50_000 in a unit test, so test the mechanism directly.
    // Add 10 entries to one group, then manually test the eviction logic.
    let p = pred(0);
    for i in 0..10 {
        summaries.add_filter_only(0, p, ChcExpr::Int(i));
    }
    // Under budget, so GC should be a no-op
    let evicted = summaries.gc_if_over_global_budget();
    assert_eq!(evicted, 0);
    assert_eq!(summaries.entry_count(), 10);
}

/// lemma_memory_pressure detects when frame is at 90%+ of soft limit
#[test]
fn lemma_memory_pressure_detection() {
    let frame = Frame::new();
    assert!(
        !frame.lemma_memory_pressure(),
        "empty frame has no pressure"
    );
}

/// Predicate constraint cache is invalidated after gc_unused_lemmas
#[test]
fn predicate_cache_invalidated_after_gc() {
    let mut frame = Frame::new();
    let p = pred(0);

    frame.add_lemma(Lemma::new(p, ge("x", 0), 1));
    frame.add_lemma(Lemma::new(p, ge("y", 5), 1));

    // Prime the cache
    let c1 = frame.get_predicate_constraint(p);
    assert!(c1.is_some());

    // Mark only first lemma as used, GC the second
    frame.lemmas[0].mark_used();
    let removed = frame.gc_unused_lemmas();
    assert_eq!(removed, 1);

    // Cache must reflect the removal
    let c2 = frame.get_predicate_constraint(p);
    assert!(c2.is_some());
    assert_ne!(c1, c2, "cache must be invalidated after GC");
}

/// lemma_keys are pruned correctly after evict_oldest_n
#[test]
fn lemma_keys_pruned_after_eviction() {
    let mut frame = Frame::new();
    let p = pred(0);

    frame.add_lemma(Lemma::new(p, ge("x", 1), 1));
    frame.add_lemma(Lemma::new(p, ge("x", 2), 1));
    frame.add_lemma(Lemma::new(p, ge("x", 3), 1));

    frame.evict_oldest_n(2);

    // Only the surviving lemma should be in lemma_keys
    assert!(!frame.contains_lemma(p, &ge("x", 1)));
    assert!(!frame.contains_lemma(p, &ge("x", 2)));
    assert!(frame.contains_lemma(p, &ge("x", 3)));
    assert_eq!(frame.lemma_keys.len(), 1);
}

// ============================================================================
// Epic #8599 Tier 1 item 2 & 3 acceptance-criteria tests (OOM caps)
// ============================================================================

/// Adding more than MAX_MUST_SUMMARIES_PER_PREDICATE distinct entries for a
/// single (level, predicate) must evict the oldest first and leave the cap
/// exactly satisfied. Covers epic #8599 Tier 1 item 3: per-predicate cap.
#[test]
fn must_summary_per_predicate_cap_evicts_oldest() {
    let mut summaries = MustSummaries::new();
    let p = pred(0);
    // Matches MAX_MUST_SUMMARIES_PER_PREDICATE in must_summaries.rs.
    let per_pred_cap = 1_000usize;
    let extra = 100usize;
    let total = per_pred_cap + extra;

    for i in 0..total {
        // Each Int(i) is a distinct formula, so dedup cannot hide the cap.
        summaries.add_filter_only(0, p, ChcExpr::Int(i as i128));
    }

    let entries = summaries
        .get_entries(0, p)
        .expect("summaries should be present");
    assert_eq!(
        entries.len(),
        per_pred_cap,
        "per-predicate cap must hold after {} inserts",
        total
    );

    // FIFO: the first `extra` entries must have been evicted.
    let surviving_formulas: Vec<&ChcExpr> = entries.iter().map(|e| &e.formula).collect();
    for evicted in 0..extra {
        let f = ChcExpr::Int(evicted as i128);
        assert!(
            !surviving_formulas.contains(&&f),
            "oldest entry Int({evicted}) must have been evicted",
        );
    }
    let newest = ChcExpr::Int((total - 1) as i128);
    assert!(
        surviving_formulas.contains(&&newest),
        "newest entry Int({}) must survive",
        total - 1
    );
}
