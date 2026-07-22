// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for hyper-ternary resolution.

use super::*;
use crate::test_util::lit;

#[test]
fn test_htr_occurrence_list() {
    let mut occ = HTROccList::new(5);

    let clause1 = vec![lit(0, true), lit(1, false), lit(2, true)];
    let clause2 = vec![lit(0, true), lit(3, true), lit(4, false)];

    occ.add_clause(0, &clause1);
    occ.add_clause(1, &clause2);

    // lit(0, true) appears in both clauses
    assert_eq!(occ.count(lit(0, true)), 2);
    assert!(occ.get(lit(0, true)).contains(&0));
    assert!(occ.get(lit(0, true)).contains(&1));
}

#[test]
fn test_htr_basic_resolve() {
    let mut htr = HTR::new(10);

    // C1 = {x0, x1, x2}, C2 = {~x0, x3, x4}
    // Resolvent on x0 should be {x1, x2, x3, x4} - too large, rejected
    let c1 = vec![lit(0, true), lit(1, true), lit(2, true)];
    let c2 = vec![lit(0, false), lit(3, true), lit(4, true)];

    let result = htr.try_resolve(&c1, &c2, lit(0, true));
    assert!(result.is_none()); // 4 literals - too large
    assert_eq!(htr.stats.too_large_skipped, 1);
}

#[test]
fn test_htr_binary_resolvent() {
    let mut htr = HTR::new(10);

    // C1 = {x0, x1, x2}, C2 = {~x0, x1, x2}
    // Resolvent on x0 should be {x1, x2} - binary!
    let c1 = vec![lit(0, true), lit(1, true), lit(2, true)];
    let c2 = vec![lit(0, false), lit(1, true), lit(2, true)];

    let result = htr.try_resolve(&c1, &c2, lit(0, true));
    assert!(result.is_some());

    let resolvent = result.unwrap();
    assert_eq!(resolvent.len(), 2);
    assert!(resolvent.contains(&lit(1, true)));
    assert!(resolvent.contains(&lit(2, true)));
}

#[test]
fn test_htr_ternary_resolvent() {
    let mut htr = HTR::new(10);

    // C1 = {x0, x1, x2}, C2 = {~x0, x1, x3}
    // Resolvent on x0 should be {x1, x2, x3} - ternary
    let c1 = vec![lit(0, true), lit(1, true), lit(2, true)];
    let c2 = vec![lit(0, false), lit(1, true), lit(3, true)];

    let result = htr.try_resolve(&c1, &c2, lit(0, true));
    assert!(result.is_some());

    let resolvent = result.unwrap();
    assert_eq!(resolvent.len(), 3);
    assert!(resolvent.contains(&lit(1, true)));
    assert!(resolvent.contains(&lit(2, true)));
    assert!(resolvent.contains(&lit(3, true)));
}

#[test]
fn test_htr_tautology_detection() {
    let mut htr = HTR::new(10);

    // C1 = {x0, x1, x2}, C2 = {~x0, ~x1, x3}
    // Resolvent would be {x1, ~x1, x2, x3} - tautology
    let c1 = vec![lit(0, true), lit(1, true), lit(2, true)];
    let c2 = vec![lit(0, false), lit(1, false), lit(3, true)];

    let result = htr.try_resolve(&c1, &c2, lit(0, true));
    assert!(result.is_none());
    assert_eq!(htr.stats.tautologies_skipped, 1);
}

#[test]
fn test_htr_duplicate_detection() {
    let mut htr = HTR::new(10);

    // Pre-populate with existing binary clause {x1, x2}
    htr.existing_binary
        .insert(HTR::normalize_binary(lit(1, true), lit(2, true)));

    // Try to derive the same binary
    let c1 = vec![lit(0, true), lit(1, true), lit(2, true)];
    let c2 = vec![lit(0, false), lit(1, true), lit(2, true)];

    let result = htr.try_resolve(&c1, &c2, lit(0, true));
    assert!(result.is_none());
    assert_eq!(htr.stats.duplicates_skipped, 1);
}

#[test]
fn test_htr_run_integration() {
    let mut htr = HTR::new(10);

    // Create clauses that allow hyper-ternary resolution
    // C0 = {x0, x1, x2}, C1 = {~x0, x1, x3}
    // These should produce ternary resolvent {x1, x2, x3}
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(1, true), lit(3, true)], false);

    htr.rebuild(&clauses);

    let vals = vec![0i8; 20];
    let result = htr.run(&clauses, &vals, 100);

    // Should produce at least one resolvent
    assert!(!result.resolvents.is_empty());
    assert!(result.resolvents.iter().any(|(r, _, _)| r.len() == 3));
}

#[test]
fn test_htr_binary_deletion() {
    let mut htr = HTR::new(10);

    // Create clauses where binary resolvent can be derived
    // C0 = {x0, x1, x2}, C1 = {~x0, x1, x2}
    // Binary resolvent {x1, x2} subsumes both
    let mut clauses = ClauseArena::new();
    let c0 = clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false);
    let c1 = clauses.add(&[lit(0, false), lit(1, true), lit(2, true)], false);

    htr.rebuild(&clauses);

    let vals = vec![0i8; 20];
    let result = htr.run(&clauses, &vals, 100);

    // Should have binary resolvent and both antecedents marked for deletion
    assert!(result.resolvents.iter().any(|(r, _, _)| r.len() == 2));
    assert_eq!(result.to_delete.len(), 2);
    assert!(result.to_delete.contains(&c0));
    assert!(result.to_delete.contains(&c1));
}

#[test]
fn test_htr_skips_assigned() {
    let mut htr = HTR::new(10);

    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(1, true), lit(3, true)], false);

    htr.rebuild(&clauses);

    // Variable 0 is assigned - should skip resolution
    let mut vals = vec![0i8; 20];
    vals[0] = 1; // var 0 positive literal = true (assigned)

    let result = htr.run(&clauses, &vals, 100);

    // Should produce no resolvents since pivot variable is assigned
    assert!(result.resolvents.is_empty());
}

#[test]
fn test_htr_stats() {
    let mut htr = HTR::new(10);

    // Create clauses for resolution
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(1, true), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(1, true), lit(3, true)], false);

    let vals = vec![0i8; 20];
    let _ = htr.run(&clauses, &vals, 100);

    let stats = htr.stats();
    assert!(stats.rounds >= 1);
    assert!(stats.pairs_checked > 0);
    // Should have at least one binary resolvent from C0 and C1
    assert!(stats.binary_resolvents >= 1 || stats.ternary_resolvents >= 1);
}

#[test]
fn test_htr_subsumption_by_binary() {
    let mut htr = HTR::new(10);

    // Pre-populate with binary clause that subsumes potential ternary resolvent
    // Binary {x1, x2} subsumes any ternary {x1, x2, ?}
    htr.existing_binary
        .insert(HTR::normalize_binary(lit(1, true), lit(2, true)));

    // C1 = {x0, x1, x3}, C2 = {~x0, x2, x3}
    // Resolvent would be {x1, x2, x3} - subsumed by {x1, x2}
    // Actually wait, {x1, x2} doesn't contain x3, so it doesn't subsume
    // Let me fix the test

    // Actually the subsumption check is: if any binary subset exists, skip
    // So {x1, x2} being a subset of {x1, x2, x3} means the ternary is subsumed

    // Resolvent would be {x1, x2, x3}
    // Check if subsumed by existing binary {x1, x2}
    assert!(htr.ternary_exists(lit(1, true), lit(2, true), lit(3, true)));
}

#[test]
fn test_normalize_binary() {
    let a = lit(3, true);
    let b = lit(1, false);

    let (x, y) = HTR::normalize_binary(a, b);
    let (x2, y2) = HTR::normalize_binary(b, a);

    // Should be the same regardless of order
    assert_eq!((x, y), (x2, y2));
    assert!(x <= y);
}

#[test]
fn test_htr_inter_round_feedback() {
    let mut htr = HTR::new(10);

    // Round 1: C0={x0,x1,x2}, C1={~x0,x1,x3} -> T={x1,x2,x3}
    // Round 2: C2={~x1,x2,x3}, T -> B={x2,x3}
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(1, true), lit(3, true)], false);
    clauses.add(&[lit(1, false), lit(2, true), lit(3, true)], false);

    let vals = vec![0i8; 20];
    let result = htr.run(&clauses, &vals, 100);

    assert!(result.resolvents.iter().any(|(r, _, _)| r.len() == 3));
    assert!(result.resolvents.iter().any(|(r, _, _)| r.len() == 2));
    for &idx in &result.to_delete {
        assert!(
            idx < clauses.len(),
            "virtual clause index leaked into to_delete"
        );
    }
}

#[test]
fn test_normalize_ternary() {
    let a = lit(5, true);
    let b = lit(2, false);
    let c = lit(7, true);

    let t1 = HTR::normalize_ternary(a, b, c);
    let t2 = HTR::normalize_ternary(c, a, b);
    let t3 = HTR::normalize_ternary(b, c, a);

    // Should all be the same
    assert_eq!(t1, t2);
    assert_eq!(t2, t3);
    assert!(t1.0 <= t1.1 && t1.1 <= t1.2);
}
