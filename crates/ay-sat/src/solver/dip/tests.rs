// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::solver::VarData;

/// Helper to create a VarData with specific level and trail_pos.
fn make_var_data(level: u32, trail_pos: u32) -> VarData {
    let mut vd = VarData::UNASSIGNED;
    vd.level = level;
    vd.trail_pos = trail_pos;
    vd
}

#[test]
fn test_dip_manager_new() {
    let mgr = DipManager::new();
    // DIP-ERCL disabled (#8448): extension variables are not RUP-derivable,
    // causing false UNSAT. mgr.enabled starts false pending correct
    // reimplementation with proper DRAT proof support.
    assert!(!mgr.enabled);
    assert_eq!(mgr.extension_var_count, 0);
    assert!(mgr.extension_var_defs.is_empty());
}

#[test]
fn test_canonical_pair_ordering() {
    let a = Literal(10);
    let b = Literal(20);
    assert_eq!(DipManager::canonical_pair(a, b), (10, 20));
    assert_eq!(DipManager::canonical_pair(b, a), (10, 20));
}

#[test]
fn test_register_and_lookup_extension() {
    let mut mgr = DipManager::new();
    let a = Literal(10);
    let b = Literal(20);
    mgr.register_extension(a, b, 100);
    assert_eq!(mgr.lookup_extension(a, b), Some(100));
    assert_eq!(mgr.lookup_extension(b, a), Some(100)); // Order-independent
    assert_eq!(mgr.lookup_extension(Literal(30), b), None);
}

#[test]
fn test_occurrence_tracking() {
    let mut mgr = DipManager::new();
    let a = Literal(10);
    let b = Literal(20);

    assert!(!mgr.pair_meets_threshold(a, b));

    for _ in 0..MIN_OCCURRENCE_THRESHOLD {
        mgr.record_pair_occurrence(a, b);
    }
    assert!(mgr.pair_meets_threshold(a, b));
    // Order independence
    assert!(mgr.pair_meets_threshold(b, a));
}

#[test]
fn test_gc_extension_vars() {
    let mut mgr = DipManager::new();
    let lits: Vec<Literal> = (0..20).map(|i| Literal(i * 2)).collect();

    // Register 10 extension variables with varying activity.
    for i in 0..10 {
        let a = lits[i * 2];
        let b = lits[i * 2 + 1];
        let ext_var = 1000 + i as u32;
        mgr.register_extension(a, b, ext_var);
        // Set activity proportional to index.
        mgr.extension_activity.insert(ext_var, (i + 1) as f64);
    }
    assert_eq!(mgr.extension_var_defs.len(), 10);

    let deleted = mgr.gc_extension_vars();
    // Bottom 25% of 10 = 2 deleted.
    assert_eq!(deleted.len(), 2);
    // Lowest activity vars (1000 with act=1, 1001 with act=2) should be deleted.
    let deleted_vars: Vec<u32> = deleted.iter().map(|&(v, _, _)| v).collect();
    assert!(deleted_vars.contains(&1000));
    assert!(deleted_vars.contains(&1001));
    assert_eq!(mgr.extension_var_defs.len(), 8);
}

#[test]
fn test_find_dip_too_few_lits() {
    // Only 1 current-level literal: no DIP possible.
    let var_data = vec![make_var_data(1, 0), make_var_data(1, 1)];
    let result = find_dip_closest_to_conflict(
        &[Literal::negative(Variable(1))],
        &var_data,
        0, // uip_var
        1, // decision_level
        &[],
    );
    assert!(result.is_none());
}

#[test]
fn test_find_dip_basic() {
    // 5 variables at decision level 3.
    // UIP is var 0, others are vars 1..4 at trail positions 5,6,7,8.
    let var_data = vec![
        make_var_data(3, 4), // var 0: UIP
        make_var_data(3, 5), // var 1
        make_var_data(3, 6), // var 2
        make_var_data(3, 7), // var 3
        make_var_data(3, 8), // var 4
    ];

    let current_level_lits = vec![
        Literal::negative(Variable(1)),
        Literal::negative(Variable(2)),
        Literal::negative(Variable(3)),
        Literal::negative(Variable(4)),
    ];

    let result = find_dip_closest_to_conflict(
        &current_level_lits,
        &var_data,
        0, // uip_var
        3, // decision_level
        &[],
    );

    assert!(result.is_some());
    let dip = result.expect("DIP should be found");

    // The two closest to conflict are vars 3 (pos 7) and 4 (pos 8).
    let dip_vars: Vec<usize> = vec![dip.pair.a.variable().index(), dip.pair.b.variable().index()];
    assert!(dip_vars.contains(&3) || dip_vars.contains(&4));
}

#[test]
fn test_try_dip_ercl_too_short_clause() {
    let mut mgr = DipManager::new();
    // Clause with only 3 literals: too short for DIP.
    let clause = vec![
        Literal::negative(Variable(0)),
        Literal::negative(Variable(1)),
        Literal::negative(Variable(2)),
    ];
    let var_data = vec![
        make_var_data(2, 0),
        make_var_data(1, 1),
        make_var_data(1, 2),
    ];
    let result = mgr.try_dip_ercl(&clause, &[], &var_data, 2, 10);
    assert!(result.is_none());
}

#[test]
fn test_try_dip_ercl_with_threshold_met() {
    let mut mgr = DipManager::new();
    mgr.enabled = true; // Override default-disabled for unit test

    // Build a scenario with 5 variables, decision level 3.
    // UIP = var 0 at level 3. Vars 1-4 at level 3 with varying trail pos.
    // Var 5 at level 1 (other level).
    let var_data = vec![
        make_var_data(3, 4), // var 0: UIP
        make_var_data(3, 5), // var 1
        make_var_data(3, 6), // var 2
        make_var_data(3, 7), // var 3
        make_var_data(3, 8), // var 4
        make_var_data(1, 2), // var 5: lower level
    ];

    let clause = vec![
        Literal::negative(Variable(0)), // UIP
        Literal::negative(Variable(1)),
        Literal::negative(Variable(2)),
        Literal::negative(Variable(3)),
        Literal::negative(Variable(4)),
        Literal::negative(Variable(5)),
    ];

    // First, pump up the pair occurrence count to meet threshold.
    // The DIP will be vars 3,4 (closest to conflict).
    let dip_a = Literal::negative(Variable(3));
    let dip_b = Literal::negative(Variable(4));
    for _ in 0..MIN_OCCURRENCE_THRESHOLD {
        mgr.record_pair_occurrence(dip_a, dip_b);
    }

    let result = mgr.try_dip_ercl(&clause, &[], &var_data, 3, 100);

    assert!(result.is_some());
    let ercl = result.expect("ERCL should succeed");

    // Extension variable should be 100.
    assert_eq!(ercl.ext_var, Variable(100));

    // Pre-DIP clause should contain UIP + non-current-level + pre-DIP lits + z.
    assert!(ercl
        .pre_dip_clause
        .contains(&Literal::negative(Variable(0))));
    assert!(ercl
        .pre_dip_clause
        .contains(&Literal::positive(Variable(100))));

    // Post-DIP clause should contain NOT z + post-DIP lits.
    assert!(ercl
        .post_dip_clause
        .contains(&Literal::negative(Variable(100))));

    // Definition clauses should have 3 elements.
    assert_eq!(ercl.definition_clauses.len(), 3);
    assert_eq!(ercl.definition_clauses[0].len(), 2);
    assert_eq!(ercl.definition_clauses[1].len(), 2);
    assert_eq!(ercl.definition_clauses[2].len(), 3);
}

#[test]
fn test_dip_disabled() {
    let mut mgr = DipManager::new();
    mgr.enabled = false;

    let clause = vec![
        Literal::negative(Variable(0)),
        Literal::negative(Variable(1)),
        Literal::negative(Variable(2)),
        Literal::negative(Variable(3)),
        Literal::negative(Variable(4)),
    ];
    let var_data = vec![
        make_var_data(2, 0),
        make_var_data(2, 1),
        make_var_data(2, 2),
        make_var_data(2, 3),
        make_var_data(2, 4),
    ];

    let result = mgr.try_dip_ercl(&clause, &[], &var_data, 2, 100);
    assert!(result.is_none());
    assert_eq!(mgr.stats.dip_skipped, 1);
}

#[test]
fn test_extension_var_reuse() {
    let mut mgr = DipManager::new();
    mgr.enabled = true; // Override default-disabled for unit test
    let a = Literal::negative(Variable(3));
    let b = Literal::negative(Variable(4));

    // Pre-register an extension variable.
    mgr.register_extension(a, b, 50);

    // Pump occurrences.
    for _ in 0..MIN_OCCURRENCE_THRESHOLD {
        mgr.record_pair_occurrence(a, b);
    }

    let var_data = vec![
        make_var_data(3, 4), // var 0: UIP
        make_var_data(3, 5),
        make_var_data(3, 6),
        make_var_data(3, 7),
        make_var_data(3, 8),
        make_var_data(1, 2),
    ];

    let clause = vec![
        Literal::negative(Variable(0)),
        Literal::negative(Variable(1)),
        Literal::negative(Variable(2)),
        a,
        b,
        Literal::negative(Variable(5)),
    ];

    let result = mgr.try_dip_ercl(&clause, &[], &var_data, 3, 100);
    assert!(result.is_some());
    let ercl = result.expect("ERCL should succeed with reuse");
    // Should reuse existing extension variable 50, not allocate 100.
    assert_eq!(ercl.ext_var, Variable(50));
    assert_eq!(mgr.stats.dip_reuses, 1);
}

#[test]
fn test_tick_conflict_gc_trigger() {
    let mut mgr = DipManager::new();

    // Add enough extension vars to exceed the threshold.
    for i in 0..3000 {
        let a = Literal(i * 4);
        let b = Literal(i * 4 + 2);
        mgr.register_extension(a, b, 10000 + i);
    }

    // Tick up to GC_INTERVAL.
    for _ in 0..GC_INTERVAL - 1 {
        assert!(!mgr.tick_conflict());
    }
    assert!(mgr.tick_conflict());
}
