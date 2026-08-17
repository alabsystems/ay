// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_empty_table() {
    let table = TheoryDispatchTable::new();
    assert!(table.is_empty());
    assert_eq!(table.len(), 0);
    assert!(!table.is_theory_atom(0));
    assert!(table.get(0).is_none());
}

#[test]
fn test_compile_basic() {
    let mut table = TheoryDispatchTable::new();
    let atoms = vec![(5, 100), (10, 200), (15, 300)];
    table.compile(atoms, &[]);

    assert_eq!(table.len(), 3);
    assert!(!table.is_empty());

    assert!(table.is_theory_atom(5));
    assert!(table.is_theory_atom(10));
    assert!(table.is_theory_atom(15));
    assert!(!table.is_theory_atom(0));
    assert!(!table.is_theory_atom(7));

    let entry = table.get(5).expect("should exist");
    assert_eq!(entry.term_id, 100);
    assert!(!entry.is_ite_guarded());

    let entry = table.get(10).expect("should exist");
    assert_eq!(entry.term_id, 200);
}

#[test]
fn test_compile_with_ite_guards() {
    let mut table = TheoryDispatchTable::new();
    let atoms = vec![(5, 100), (10, 200), (15, 300)];
    let ite_guards = vec![(10, 3, true), (15, 7, false)];
    table.compile(atoms, &ite_guards);

    // Var 5: no ITE guard.
    let e5 = table.get(5).expect("should exist");
    assert!(!e5.is_ite_guarded());

    // Var 10: ITE guarded, cond=3, then branch.
    let e10 = table.get(10).expect("should exist");
    assert!(e10.is_ite_guarded());
    assert_eq!(e10.ite_cond_var, 3);
    assert!(e10.is_then_branch);

    // Var 15: ITE guarded, cond=7, else branch.
    let e15 = table.get(15).expect("should exist");
    assert!(e15.is_ite_guarded());
    assert_eq!(e15.ite_cond_var, 7);
    assert!(!e15.is_then_branch);
}

#[test]
fn test_dispatch_non_theory_atom() {
    let mut table = TheoryDispatchTable::new();
    table.compile(vec![(5, 100)], &[]);

    let result = table.dispatch_assignment(0, true, &|_| None, 1);
    assert_eq!(result, TheoryDispatchResult::Skip);
}

#[test]
fn test_dispatch_theory_atom_no_ite() {
    let mut table = TheoryDispatchTable::new();
    table.compile(vec![(5, 100)], &[]);

    let result = table.dispatch_assignment(5, true, &|_| None, 1);
    assert_eq!(
        result,
        TheoryDispatchResult::Assert {
            term_id: 100,
            value: true,
        }
    );

    let result = table.dispatch_assignment(5, false, &|_| None, 1);
    assert_eq!(
        result,
        TheoryDispatchResult::Assert {
            term_id: 100,
            value: false,
        }
    );
}

#[test]
fn test_dispatch_ite_defer_inactive_branch() {
    let mut table = TheoryDispatchTable::new();
    // Var 10 is in the "then" branch, guarded by cond var 3.
    table.compile(vec![(10, 200)], &[(10, 3, true)]);

    // Cond var 3 = false (selects else branch).
    // Var 10 is in then branch -> inactive -> defer.
    let result = table.dispatch_assignment(
        10,
        true,
        &|v| {
            if v == 3 {
                Some(false)
            } else {
                None
            }
        },
        1,
    );
    assert_eq!(
        result,
        TheoryDispatchResult::DeferIte {
            term_id: 200,
            value: true,
        }
    );
}

#[test]
fn test_dispatch_ite_assert_active_branch() {
    let mut table = TheoryDispatchTable::new();
    // Var 10 is in the "then" branch, guarded by cond var 3.
    table.compile(vec![(10, 200)], &[(10, 3, true)]);

    // Cond var 3 = true (selects then branch).
    // Var 10 is in then branch -> active -> assert.
    let result = table.dispatch_assignment(
        10,
        true,
        &|v| {
            if v == 3 {
                Some(true)
            } else {
                None
            }
        },
        1,
    );
    assert_eq!(
        result,
        TheoryDispatchResult::Assert {
            term_id: 200,
            value: true,
        }
    );
}

#[test]
fn test_dispatch_ite_unassigned_cond_asserts() {
    let mut table = TheoryDispatchTable::new();
    table.compile(vec![(10, 200)], &[(10, 3, true)]);

    // Unassigned condition at level > 0 → assert (CDCL handles conflicts).
    let result = table.dispatch_assignment(10, true, &|_| None, 1);
    assert_eq!(
        result,
        TheoryDispatchResult::Assert {
            term_id: 200,
            value: true,
        }
    );
}

#[test]
fn test_dispatch_ite_at_level_zero_asserts() {
    let mut table = TheoryDispatchTable::new();
    table.compile(vec![(10, 200)], &[(10, 3, true)]);

    // At level 0, ITE deferral is disabled entirely.
    let result = table.dispatch_assignment(
        10,
        true,
        &|v| {
            if v == 3 {
                Some(false)
            } else {
                None
            }
        },
        0,
    );
    assert_eq!(
        result,
        TheoryDispatchResult::Assert {
            term_id: 200,
            value: true,
        }
    );
}

#[test]
fn test_set_ite_guard_after_compile() {
    let mut table = TheoryDispatchTable::new();
    table.compile(vec![(5, 100)], &[]);

    // Initially no guard.
    assert!(!table.get(5).expect("exists").is_ite_guarded());

    // Add guard after compilation.
    table.set_ite_guard(5, 2, false);
    let entry = table.get(5).expect("exists");
    assert!(entry.is_ite_guarded());
    assert_eq!(entry.ite_cond_var, 2);
    assert!(!entry.is_then_branch);
}

#[test]
fn test_set_ite_guard_nonexistent_var_is_noop() {
    let mut table = TheoryDispatchTable::new();
    table.compile(vec![(5, 100)], &[]);

    // Setting guard on non-theory-atom is a no-op.
    table.set_ite_guard(99, 2, true);
    assert!(!table.is_theory_atom(99));
}

#[test]
fn test_dispatch_out_of_bounds() {
    let mut table = TheoryDispatchTable::new();
    table.compile(vec![(5, 100)], &[]);

    // Var ID beyond table capacity.
    let result = table.dispatch_assignment(1000, true, &|_| None, 1);
    assert_eq!(result, TheoryDispatchResult::Skip);
}

#[test]
fn test_recompile_clears_old_data() {
    let mut table = TheoryDispatchTable::new();
    table.compile(vec![(5, 100), (10, 200)], &[]);
    assert_eq!(table.len(), 2);

    // Recompile with different atoms.
    table.compile(vec![(3, 50)], &[]);
    assert_eq!(table.len(), 1);
    assert!(table.is_theory_atom(3));
    assert!(!table.is_theory_atom(5));
    assert!(!table.is_theory_atom(10));
}

#[test]
fn test_capacity() {
    let mut table = TheoryDispatchTable::new();
    table.compile(vec![(100, 42)], &[]);
    assert_eq!(table.capacity(), 101); // 0..=100
}

#[test]
fn test_theory_inline_plan_pure_sat_erases_callback() {
    let profile = TheoryInlineProfile::pure_sat();
    let plan = TheoryInlinePlan::from_profile(&profile);

    assert_eq!(plan.mode, TheoryInlineMode::PureSat);
    assert!(!plan.uses_theory_callback);
    assert!(plan.bakes_can_propagate);
    assert!(!plan.requires_fixpoint_interleaving);
    assert!(!plan.preserves_ite_relevancy);
}

#[test]
fn test_theory_inline_plan_single_direct_theory() {
    let profile = TheoryInlineProfile::single_direct(TheoryInlineKind::Lra, 17);
    let plan = TheoryInlinePlan::from_profile(&profile);

    assert_eq!(
        plan.mode,
        TheoryInlineMode::SingleTheoryDirect(TheoryInlineKind::Lra)
    );
    assert!(!plan.uses_theory_callback);
    assert!(plan.bakes_can_propagate);
    assert!(!plan.requires_fixpoint_interleaving);
}

#[test]
fn test_theory_inline_plan_combined_direct_keeps_fixpoint() {
    let profile = TheoryInlineProfile {
        participants: vec![
            TheoryInlineParticipant::direct(TheoryInlineKind::Euf),
            TheoryInlineParticipant::direct(TheoryInlineKind::Lra),
        ],
        theory_atom_count: 12,
        has_ite_guards: true,
    };
    let plan = TheoryInlinePlan::from_profile(&profile);

    assert_eq!(plan.mode, TheoryInlineMode::CombinedTheoryDirect);
    assert!(!plan.uses_theory_callback);
    assert!(plan.bakes_can_propagate);
    assert!(plan.requires_fixpoint_interleaving);
    assert!(plan.preserves_ite_relevancy);
}

#[test]
fn test_theory_inline_plan_generic_fallback_for_non_direct_theory() {
    let profile = TheoryInlineProfile {
        participants: vec![
            TheoryInlineParticipant::direct(TheoryInlineKind::Lra),
            TheoryInlineParticipant::generic(TheoryInlineKind::Other),
        ],
        theory_atom_count: 9,
        has_ite_guards: false,
    };
    let plan = TheoryInlinePlan::from_profile(&profile);

    assert_eq!(plan.mode, TheoryInlineMode::GenericCallback);
    assert!(plan.uses_theory_callback);
    assert!(!plan.bakes_can_propagate);
    assert!(plan.requires_fixpoint_interleaving);
}
