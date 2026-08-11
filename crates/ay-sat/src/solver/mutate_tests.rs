// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for clause mutation helpers (delete, replace, add).

use super::*;
use crate::literal::Variable;
use crate::ProofOutput;
use ay_test_support::{build_ay_lrat_checker, BuiltWorkspaceBinary};

use std::path::{Path, PathBuf};
use std::sync::OnceLock;

fn count_clause_watches(solver: &Solver, lit: Literal, clause_ref: ClauseRef) -> usize {
    let watch_list = solver.watches.get_watches(lit);
    (0..watch_list.len())
        .filter(|&wi| watch_list.clause_ref(wi) == clause_ref)
        .count()
}

fn assign_level0_test_lit(solver: &mut Solver, lit: Literal) {
    let vi = lit.variable().index();
    solver.vals[lit.index()] = 1;
    solver.vals[lit.negated().index()] = -1;
    solver.var_data[vi].level = 0;
    solver.var_data[vi].trail_pos = solver.trail.len() as u32;
    solver.trail.push(lit);
}

fn record_hidden_trusted_unit(solver: &mut Solver, lit: Literal) -> u64 {
    let hidden_id = solver.proof_emit_unit(lit, &[], ProofAddKind::TrustedTransform);
    assert_ne!(
        hidden_id, 0,
        "trusted-transform unit must reserve an LRAT ID"
    );
    assert!(
        !solver.lrat_hint_id_visible(hidden_id),
        "trusted-transform unit must stay hidden from external LRAT hints"
    );
    hidden_id
}

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("AY workspace root")
        .canonicalize()
        .expect("AY workspace root should be canonicalizable")
}

/// Return the standalone checker built from this test's exact source tree.
fn require_workspace_lrat_checker() -> &'static BuiltWorkspaceBinary {
    static CHECKER: OnceLock<BuiltWorkspaceBinary> = OnceLock::new();
    CHECKER.get_or_init(|| build_ay_lrat_checker(&workspace_root()))
}

/// Regression test for #3812: replace_clause_checked must reorder literals
/// so that unassigned/highest-level literals are in watch positions [0] and [1].
/// Without this, BCP may miss unit propagations after clause strengthening.
#[test]
fn test_replace_clause_checked_reorders_for_watches() {
    let mut solver: Solver = Solver::new(5);

    // Set up assignments: var0 false@0, var1 false@0, var2 unassigned,
    // var3 false@1, var4 unassigned.
    solver.var_data[0].level = 0;
    solver.vals[Literal::positive(Variable(0)).index()] = -1; // var0 = false
    solver.vals[Literal::negative(Variable(0)).index()] = 1;
    solver.var_data[1].level = 0;
    solver.vals[Literal::positive(Variable(1)).index()] = -1; // var1 = false
    solver.vals[Literal::negative(Variable(1)).index()] = 1;
    // var2: unassigned
    solver.var_data[3].level = 1;
    solver.vals[Literal::positive(Variable(3)).index()] = -1; // var3 = false
    solver.vals[Literal::negative(Variable(3)).index()] = 1;
    // var4: unassigned

    // Add a clause [v0, v1, v2, v3, v4]
    let mut lits: Vec<Literal> = (0..5).map(|i| Literal::positive(Variable(i))).collect();
    let result = solver.add_clause_watched(&mut lits);
    let clause_ref = match result {
        AddResult::Added(cr) => cr,
        _ => panic!("expected Added"),
    };

    // Now replace with [v0, v1, v3] — all falsified, but the clause is
    // bogus for this test; we just verify watch placement.
    // Without the reorder fix, watches would be on v0 (false@0) and v1 (false@0).
    // With the fix, v3 (false@1, highest level) should be in position [0] or [1].
    let new_lits = vec![
        Literal::positive(Variable(0)), // false@0
        Literal::positive(Variable(1)), // false@0
        Literal::positive(Variable(3)), // false@1
    ];
    solver.replace_clause_checked(clause_ref.0 as usize, &new_lits);

    // After reorder, the first two positions should have the best-scoring
    // literals. v3 (false@level1) scores higher than v0/v1 (false@level0).
    let idx = clause_ref.0 as usize;
    let lit0 = solver.arena.literal(idx, 0);
    let lit1 = solver.arena.literal(idx, 1);
    // v3 must be in one of the first two positions
    assert!(
        lit0 == Literal::positive(Variable(3)) || lit1 == Literal::positive(Variable(3)),
        "v3 (highest level false) should be in watch position, got [{lit0:?}, {lit1:?}]"
    );
}

/// Test that replace_clause_checked prefers unassigned literals for watches.
#[test]
fn test_replace_clause_checked_prefers_unassigned_watches() {
    let mut solver: Solver = Solver::new(4);

    // var0 false@0, var1 false@1, var2 unassigned, var3 unassigned
    solver.var_data[0].level = 0;
    solver.vals[Literal::positive(Variable(0)).index()] = -1;
    solver.vals[Literal::negative(Variable(0)).index()] = 1;
    solver.var_data[1].level = 1;
    solver.vals[Literal::positive(Variable(1)).index()] = -1;
    solver.vals[Literal::negative(Variable(1)).index()] = 1;

    // Add initial clause
    let mut lits: Vec<Literal> = (0..4).map(|i| Literal::positive(Variable(i))).collect();
    let result = solver.add_clause_watched(&mut lits);
    let clause_ref = match result {
        AddResult::Added(cr) => cr,
        _ => panic!("expected Added"),
    };

    // Replace: [v0(false@0), v1(false@1), v2(undef), v3(undef)]
    let new_lits = vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
        Literal::positive(Variable(3)),
    ];
    solver.replace_clause_checked(clause_ref.0 as usize, &new_lits);

    let idx = clause_ref.0 as usize;
    let lit0 = solver.arena.literal(idx, 0);
    let lit1 = solver.arena.literal(idx, 1);

    // Both unassigned vars (v2, v3) should be in watch positions
    let is_unassigned = |lit: Literal| !solver.var_is_assigned(lit.variable().index());
    assert!(
        is_unassigned(lit0) && is_unassigned(lit1),
        "unassigned literals should be in watch positions, got [{lit0:?}, {lit1:?}]"
    );
}

/// Performance characterization: ClearLevel0 reason policy scans ALL variables
/// to find matching reason references, costing O(num_vars) per clause deletion.
///
/// CaDiCaL scans only the clause's literals (O(clause_len)), which is correct
/// because only a variable IN the clause can have it as its reason. This test
/// verifies the correctness invariant: after ClearLevel0 deletion of a reason
/// clause, the propagated variable's reason is cleared.
///
/// Performance issue: the current O(num_vars) loop at mutate.rs:189 makes BVE
/// quadratic in problem size. With V variables and D deleted clauses, total cost
/// is O(V × D) instead of O(sum(clause_len_i)) ≈ O(D × avg_clause_len).
/// For 100K variables and 1000 deleted clauses: 100M iterations vs ~10K.
#[test]
fn test_clear_level0_reason_policy_clears_reason() {
    let mut solver: Solver = Solver::new(10);

    // Simulate level-0 propagation: var0 propagated by clause 0 at level 0.
    let clause_lits = vec![
        Literal::positive(Variable(0)),
        Literal::negative(Variable(1)),
        Literal::negative(Variable(2)),
    ];
    solver.add_clause(clause_lits);

    // Set up var0 as propagated at level 0 with clause 0 as reason.
    solver.vals[Literal::positive(Variable(0)).index()] = 1;
    solver.vals[Literal::negative(Variable(0)).index()] = -1;
    solver.var_data[0].level = 0;
    solver.var_data[0].reason = 0;
    solver.trail.push(Literal::positive(Variable(0)));

    // Set up var1 and var2 as assigned at level 0 (no reason — decisions or units).
    solver.vals[Literal::positive(Variable(1)).index()] = -1;
    solver.vals[Literal::negative(Variable(1)).index()] = 1;
    solver.var_data[1].level = 0;
    solver.vals[Literal::positive(Variable(2)).index()] = -1;
    solver.vals[Literal::negative(Variable(2)).index()] = 1;
    solver.var_data[2].level = 0;

    // Mark clause 0 as a reason clause via epoch stamping.
    solver.refresh_reason_clause_marks();

    // Delete with ClearLevel0 — should clear var0's reason and delete the clause.
    let result = solver.delete_clause_checked(0, ReasonPolicy::ClearLevel0);
    assert_eq!(result, DeleteResult::Deleted);

    // The reason for var0 must be cleared.
    assert_eq!(
        solver.var_reason(0),
        None,
        "ClearLevel0 must clear level-0 reason for var0"
    );

    // All other variables should be unaffected.
    for vi in 1..10 {
        assert_eq!(
            solver.var_reason(vi),
            None,
            "var {vi} reason should be unchanged"
        );
    }
}

/// Verify that only variables IN the clause can have it as a reason.
/// This is the correctness invariant that enables the O(clause_len) fix
/// for ClearLevel0 (replacing the current O(num_vars) scan).
#[test]
fn test_reason_clause_contains_propagated_variable() {
    let mut solver: Solver = Solver::new(5);

    // Add clause: (v0, ¬v1, ¬v2)
    let clause_lits = vec![
        Literal::positive(Variable(0)),
        Literal::negative(Variable(1)),
        Literal::negative(Variable(2)),
    ];
    solver.add_clause(clause_lits);

    // Simulate: v1=true, v2=true at level 0, then v0 propagated by clause 0.
    solver.vals[Literal::positive(Variable(1)).index()] = 1;
    solver.vals[Literal::negative(Variable(1)).index()] = -1;
    solver.var_data[1].level = 0;
    solver.vals[Literal::positive(Variable(2)).index()] = 1;
    solver.vals[Literal::negative(Variable(2)).index()] = -1;
    solver.var_data[2].level = 0;

    solver.vals[Literal::positive(Variable(0)).index()] = 1;
    solver.vals[Literal::negative(Variable(0)).index()] = -1;
    solver.var_data[0].level = 0;
    solver.var_data[0].reason = 0;

    // The invariant: the variable whose reason is this clause must appear
    // as a literal in the clause. This justifies scanning clause literals
    // instead of all variables in ClearLevel0.
    let cref = ClauseRef(0);
    let clause_vars: Vec<usize> = solver
        .arena
        .literals(cref.0 as usize)
        .iter()
        .map(|l| l.variable().index())
        .collect();

    for vi in 0..5 {
        if solver.var_reason(vi) == Some(cref) {
            assert!(
                clause_vars.contains(&vi),
                "var {vi} has clause 0 as reason but is not in clause 0's literals"
            );
        }
    }
}

#[test]
fn test_can_delete_clause_policy_matches_delete_modes() {
    let mut solver: Solver = Solver::new(3);
    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    solver.add_clause(vec![x0, x1.negated()]);

    // Simulate x0 propagated at level 0 by clause 0.
    solver.set_var_assignment(0, Some(true));
    solver.var_data[0].level = 0;
    solver.var_data[0].reason = 0;
    solver.trail.push(x0);
    solver.set_var_assignment(1, Some(true));
    solver.var_data[1].level = 0;
    solver.trail.push(x1);
    solver.refresh_reason_clause_marks();

    assert!(
        !solver.can_delete_clause(0, ReasonPolicy::Skip),
        "Skip policy must reject reason-protected clauses"
    );
    assert!(
        solver.can_delete_clause(0, ReasonPolicy::ClearLevel0),
        "ClearLevel0 policy must allow deleting reason-protected clauses"
    );

    let skipped = solver.delete_clause_checked(0, ReasonPolicy::Skip);
    assert_eq!(skipped, DeleteResult::Skipped);
    assert!(
        solver.arena.is_active(0),
        "Skip policy must keep reason clause active"
    );

    let deleted = solver.delete_clause_checked(0, ReasonPolicy::ClearLevel0);
    assert_eq!(deleted, DeleteResult::Deleted);
    assert_eq!(
        solver.var_reason(0),
        None,
        "ClearLevel0 deletion must clear the level-0 reason"
    );
    assert!(
        !solver.arena.is_active(0),
        "ClearLevel0 deletion must remove clause from active DB"
    );
}

#[test]
fn test_delete_clause_with_snapshot_runs_callback_only_when_deletable() {
    let mut solver: Solver = Solver::new(2);
    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    solver.add_clause(vec![x0, x1.negated()]);

    // Mark clause 0 as a level-0 reason so Skip policy blocks deletion.
    solver.set_var_assignment(0, Some(true));
    solver.var_data[0].level = 0;
    solver.var_data[0].reason = 0;
    solver.trail.push(x0);
    solver.refresh_reason_clause_marks();

    let mut skip_called = false;
    let skipped =
        solver.delete_clause_with_snapshot(0, ReasonPolicy::Skip, |_solver, _clause_lits| {
            skip_called = true;
        });
    assert_eq!(skipped, DeleteResult::Skipped);
    assert!(
        !skip_called,
        "snapshot callback must not run when deletion is skipped"
    );
    assert!(solver.arena.is_active(0), "Skip must keep clause active");

    let mut captured_lits = Vec::new();
    let deleted =
        solver.delete_clause_with_snapshot(0, ReasonPolicy::ClearLevel0, |_solver, clause_lits| {
            captured_lits = clause_lits
        });
    assert_eq!(deleted, DeleteResult::Deleted);
    assert_eq!(captured_lits, vec![x0, x1.negated()]);
    assert!(
        !solver.arena.is_active(0),
        "ClearLevel0 must delete the clause"
    );
}

#[test]
fn test_delete_clause_checked_binary_unlinks_watches_eagerly() {
    let mut solver: Solver = Solver::new(2);
    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let mut clause = vec![x0, x1];
    let clause_ref = match solver.add_clause_watched(&mut clause) {
        AddResult::Added(clause_ref) => clause_ref,
        other => panic!("expected binary clause to be Added, got {other:?}"),
    };

    assert_eq!(count_clause_watches(&solver, x0, clause_ref), 1);
    assert_eq!(count_clause_watches(&solver, x1, clause_ref), 1);

    let deleted = solver.delete_clause_checked(clause_ref.0 as usize, ReasonPolicy::Skip);
    assert_eq!(deleted, DeleteResult::Deleted);
    assert!(
        !solver.arena.is_active(clause_ref.0 as usize),
        "binary clause must be deleted"
    );
    assert_eq!(
        count_clause_watches(&solver, x0, clause_ref),
        0,
        "binary delete must eagerly unlink watch on lit0"
    );
    assert_eq!(
        count_clause_watches(&solver, x1, clause_ref),
        0,
        "binary delete must eagerly unlink watch on lit1"
    );
}

#[test]
fn test_clear_level0_reason_policy_clears_stale_reason_not_in_clause() {
    let mut solver: Solver = Solver::new(3);
    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));

    solver.add_clause(vec![a, b.negated()]);

    solver.vals[a.index()] = 1;
    solver.vals[a.negated().index()] = -1;
    solver.var_data[a.variable().index()].level = 0;
    solver.trail.push(a);

    solver.vals[b.index()] = 1;
    solver.vals[b.negated().index()] = -1;
    solver.var_data[b.variable().index()].level = 0;
    solver.trail.push(b);

    // Simulate a stale reason reference left behind by an earlier in-place rewrite.
    solver.var_data[2].level = 0;
    solver.var_data[2].reason = 0;
    solver.refresh_reason_clause_marks();

    let deleted = solver.delete_clause_checked(0, ReasonPolicy::ClearLevel0);
    assert_eq!(deleted, DeleteResult::Deleted);
    assert_eq!(solver.var_reason(2), None);
}

#[test]
fn test_clear_level0_reason_policy_clears_nonroot_stale_reason() {
    let mut solver: Solver = Solver::new(2);
    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));

    solver.add_clause(vec![a, b]);

    // Simulate a stale probe/backtrack residue: the variable is no longer
    // assigned, but its old non-root reason still points at this clause.
    solver.var_data[b.variable().index()].level = 1;
    solver.var_data[b.variable().index()].reason = 0;
    solver.refresh_reason_clause_marks();

    let deleted = solver.delete_clause_checked(0, ReasonPolicy::ClearLevel0);
    assert_eq!(deleted, DeleteResult::Deleted);
    assert_eq!(solver.var_reason(b.variable().index()), None);
}

#[test]
fn test_replace_clause_checked_clears_reason_for_removed_assigned_literal() {
    let mut solver: Solver = Solver::new(4);
    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));
    let d = Literal::positive(Variable(3));

    solver.add_clause(vec![a, b.negated(), c.negated()]);

    solver.vals[a.index()] = 1;
    solver.vals[a.negated().index()] = -1;
    solver.var_data[a.variable().index()].level = 0;
    solver.var_data[a.variable().index()].reason = 0;
    solver.trail.push(a);

    solver.vals[b.index()] = 1;
    solver.vals[b.negated().index()] = -1;
    solver.var_data[b.variable().index()].level = 0;
    solver.trail.push(b);

    solver.vals[c.index()] = 1;
    solver.vals[c.negated().index()] = -1;
    solver.var_data[c.variable().index()].level = 0;
    solver.trail.push(c);

    solver.vals[d.index()] = 1;
    solver.vals[d.negated().index()] = -1;
    solver.var_data[d.variable().index()].level = 0;
    solver.trail.push(d);

    let replace = solver.replace_clause_checked(0, &[d, b.negated(), c.negated()]);
    assert_eq!(replace, ReplaceResult::Replaced);
    assert_eq!(
        solver.var_reason(a.variable().index()),
        None,
        "replacement must clear a stale level-0 reason when the assigned literal is removed",
    );

    solver.refresh_reason_clause_marks();
    let deleted = solver.delete_clause_checked(0, ReasonPolicy::ClearLevel0);
    assert_eq!(deleted, DeleteResult::Deleted);
}

#[test]
fn test_delete_clause_checked_lrat_clearlevel0_skips_when_unit_antecedent_missing() {
    let proof = ProofOutput::lrat_text(Vec::new(), 1);
    let mut solver = Solver::with_proof_output(2, proof);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let clause_idx = solver.arena.len();
    assert!(solver.add_clause(vec![b, a.negated()]));
    let clause_ref = ClauseRef(clause_idx as u32);
    let clause_id = solver.clause_id(clause_ref);
    assert_ne!(clause_id, 0);
    assert!(solver.lrat_hint_id_visible(clause_id));
    let clause_lits_before = solver.arena.literals(clause_idx).to_vec();

    assign_level0_test_lit(&mut solver, a);
    assign_level0_test_lit(&mut solver, b);
    solver.var_data[b.variable().index()].reason = clause_ref.0;
    solver.refresh_reason_clause_marks();
    assert_eq!(solver.var_reason(b.variable().index()), Some(clause_ref));
    assert_eq!(solver.level0_unit_chain_proof_id_for_lit(a), None);

    let deleted = solver.delete_clause_checked(clause_idx, ReasonPolicy::ClearLevel0);

    assert_eq!(
        deleted,
        DeleteResult::Skipped,
        "LRAT ClearLevel0 delete must fail closed without a visible proof for antecedent a"
    );
    assert!(
        solver.arena.is_active(clause_idx),
        "failed-closed delete must preserve the reason clause"
    );
    assert_eq!(solver.arena.literals(clause_idx), clause_lits_before);
    assert_eq!(
        solver.var_reason(b.variable().index()),
        Some(clause_ref),
        "failed-closed delete must preserve the level-0 reason"
    );
}

#[test]
fn expired_deadline_preserves_lrat_delete_for_incremental_retry() {
    let proof = ProofOutput::lrat_text(Vec::new(), 2);
    let mut solver = Solver::with_proof_output(2, proof);
    let support = Literal::positive(Variable(0));
    let target = Literal::positive(Variable(1));

    let support_idx = solver.add_clause_db(&[support], false);
    let support_ref = ClauseRef(support_idx as u32);
    let support_id = solver.clause_id(support_ref);
    let reason_idx = solver.add_clause_db(&[target, support.negated()], false);
    let reason_ref = ClauseRef(reason_idx as u32);
    assign_level0_test_lit(&mut solver, support);
    assign_level0_test_lit(&mut solver, target);
    solver.var_data[support.variable().index()].reason = support_ref.0;
    solver.var_data[target.variable().index()].reason = reason_ref.0;
    solver.record_unit_proof_id_for_lit(support, support_id);
    solver.refresh_reason_clause_marks();

    solver.set_solve_deadline(Some(ay_core::time::Instant::now()));
    let started = std::time::Instant::now();
    let interrupted = solver.delete_clause_checked(reason_idx, ReasonPolicy::ClearLevel0);
    assert!(started.elapsed() < std::time::Duration::from_millis(500));
    assert_eq!(interrupted, DeleteResult::Skipped);
    assert!(solver.arena.is_active(reason_idx));
    assert_eq!(
        solver.var_reason(target.variable().index()),
        Some(reason_ref),
        "deadline truncation must not detach the live reason before retry"
    );

    solver.set_solve_deadline(None);
    let retried = solver.delete_clause_checked(reason_idx, ReasonPolicy::ClearLevel0);
    assert_eq!(retried, DeleteResult::Deleted);
    assert!(!solver.arena.is_active(reason_idx));
    assert_eq!(solver.var_reason(target.variable().index()), None);
    assert!(
        solver.visible_unit_proof_id_for_lit(target).is_some(),
        "retry must materialize a checker-visible standalone unit before deletion"
    );
}

#[test]
fn test_delete_clause_checked_lrat_clearlevel0_skips_when_unit_antecedent_hidden() {
    let proof = ProofOutput::lrat_text(Vec::new(), 1);
    let mut solver = Solver::with_proof_output(2, proof);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let clause_idx = solver.arena.len();
    assert!(solver.add_clause(vec![b, a.negated()]));
    let clause_ref = ClauseRef(clause_idx as u32);
    let clause_id = solver.clause_id(clause_ref);
    assert_ne!(clause_id, 0);
    assert!(solver.lrat_hint_id_visible(clause_id));
    let clause_lits_before = solver.arena.literals(clause_idx).to_vec();

    let hidden_id = record_hidden_trusted_unit(&mut solver, a);
    assert_eq!(solver.unit_proof_id[a.variable().index()], hidden_id);
    assign_level0_test_lit(&mut solver, a);
    assign_level0_test_lit(&mut solver, b);
    solver.var_data[b.variable().index()].reason = clause_ref.0;
    solver.refresh_reason_clause_marks();
    assert_eq!(
        solver.level0_unit_chain_proof_id_for_lit(a),
        None,
        "hidden trusted units are not valid external LRAT antecedents"
    );

    let deleted = solver.delete_clause_checked(clause_idx, ReasonPolicy::ClearLevel0);

    assert_eq!(
        deleted,
        DeleteResult::Skipped,
        "LRAT ClearLevel0 delete must fail closed when an antecedent proof is hidden"
    );
    assert!(
        solver.arena.is_active(clause_idx),
        "failed-closed delete must preserve the reason clause"
    );
    assert_eq!(solver.arena.literals(clause_idx), clause_lits_before);
    assert_eq!(
        solver.var_reason(b.variable().index()),
        Some(clause_ref),
        "failed-closed delete must preserve the level-0 reason"
    );
}

#[test]
fn test_delete_clause_checked_lrat_skips_when_unit_proof_rederive_antecedent_missing() {
    let proof = ProofOutput::lrat_text(Vec::new(), 1);
    let mut solver = Solver::with_proof_output(2, proof);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let clause_idx = solver.arena.len();
    assert!(solver.add_clause(vec![b, a.negated()]));
    let clause_ref = ClauseRef(clause_idx as u32);
    let clause_id = solver.clause_id(clause_ref);
    assert_ne!(clause_id, 0);
    let clause_lits_before = solver.arena.literals(clause_idx).to_vec();

    assign_level0_test_lit(&mut solver, a);
    assign_level0_test_lit(&mut solver, b);
    solver.record_unit_proof_id_for_lit(b, clause_id);
    assert_eq!(solver.level0_unit_chain_proof_id_for_lit(a), None);

    let deleted = solver.delete_clause_checked(clause_idx, ReasonPolicy::Skip);

    assert_eq!(
        deleted,
        DeleteResult::Skipped,
        "LRAT deletion must fail closed before deleting a clause still used as a unit proof"
    );
    assert!(solver.arena.is_active(clause_idx));
    assert_eq!(solver.arena.literals(clause_idx), clause_lits_before);
    assert_eq!(solver.unit_proof_id[b.variable().index()], clause_id);
    assert_eq!(solver.clause_id(clause_ref), clause_id);
}

#[test]
fn test_replace_clause_lrat_clearlevel0_skips_when_unit_antecedent_missing() {
    let proof = ProofOutput::lrat_text(Vec::new(), 1);
    let mut solver = Solver::with_proof_output(2, proof);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let clause_idx = solver.arena.len();
    assert!(solver.add_clause(vec![b, a.negated()]));
    let clause_ref = ClauseRef(clause_idx as u32);
    let old_clause_id = solver.clause_id(clause_ref);
    assert_ne!(old_clause_id, 0);
    let clause_lits_before = solver.arena.literals(clause_idx).to_vec();

    assign_level0_test_lit(&mut solver, a);
    assign_level0_test_lit(&mut solver, b);
    solver.var_data[b.variable().index()].reason = clause_ref.0;
    assert_eq!(solver.level0_unit_chain_proof_id_for_lit(a), None);

    let replaced = solver.replace_clause_with_final_hints(clause_idx, &[a.negated()], &[]);

    assert_eq!(
        replaced,
        ReplaceResult::Skipped,
        "LRAT replacement must fail closed before clearing a reason whose unit antecedent is missing"
    );
    assert!(
        solver.arena.is_active(clause_idx),
        "failed-closed replacement must keep the clause active"
    );
    assert_eq!(
        solver.clause_id(clause_ref),
        old_clause_id,
        "failed-closed replacement must preserve the original clause ID"
    );
    assert_eq!(solver.arena.literals(clause_idx), clause_lits_before);
    assert_eq!(
        solver.var_reason(b.variable().index()),
        Some(clause_ref),
        "failed-closed replacement must preserve the level-0 reason"
    );
}

#[test]
fn test_replace_clause_lrat_clearlevel0_skips_when_unit_antecedent_hidden() {
    let proof = ProofOutput::lrat_text(Vec::new(), 1);
    let mut solver = Solver::with_proof_output(2, proof);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let clause_idx = solver.arena.len();
    assert!(solver.add_clause(vec![b, a.negated()]));
    let clause_ref = ClauseRef(clause_idx as u32);
    let old_clause_id = solver.clause_id(clause_ref);
    assert_ne!(old_clause_id, 0);
    let clause_lits_before = solver.arena.literals(clause_idx).to_vec();

    let hidden_id = record_hidden_trusted_unit(&mut solver, a);
    assert_eq!(solver.unit_proof_id[a.variable().index()], hidden_id);
    assign_level0_test_lit(&mut solver, a);
    assign_level0_test_lit(&mut solver, b);
    solver.var_data[b.variable().index()].reason = clause_ref.0;
    assert_eq!(
        solver.level0_unit_chain_proof_id_for_lit(a),
        None,
        "hidden trusted units are not valid external LRAT antecedents"
    );

    let replaced = solver.replace_clause_with_final_hints(clause_idx, &[a.negated()], &[]);

    assert_eq!(
        replaced,
        ReplaceResult::Skipped,
        "LRAT replacement must fail closed before clearing a reason whose unit antecedent is hidden"
    );
    assert!(
        solver.arena.is_active(clause_idx),
        "failed-closed replacement must keep the clause active"
    );
    assert_eq!(
        solver.clause_id(clause_ref),
        old_clause_id,
        "failed-closed replacement must preserve the original clause ID"
    );
    assert_eq!(solver.arena.literals(clause_idx), clause_lits_before);
    assert_eq!(
        solver.var_reason(b.variable().index()),
        Some(clause_ref),
        "failed-closed replacement must preserve the level-0 reason"
    );
}

#[test]
fn test_replace_clause_with_final_hints_rederives_removed_reason_before_delete() {
    let proof = ProofOutput::lrat_text(Vec::new(), 2);
    let mut solver = Solver::with_proof_output(2, proof);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));

    let support_idx = solver.arena.len();
    assert!(solver.add_clause(vec![a]));
    let support_ref = ClauseRef(support_idx as u32);
    let support_id = solver.clause_id(support_ref);
    assert_ne!(support_id, 0);

    let clause_idx = solver.arena.len();
    assert!(solver.add_clause(vec![b, a.negated()]));
    let clause_ref = ClauseRef(clause_idx as u32);
    let old_clause_id = solver.clause_id(clause_ref);
    assert_ne!(old_clause_id, 0);

    assign_level0_test_lit(&mut solver, a);
    assign_level0_test_lit(&mut solver, b);
    solver.var_data[a.variable().index()].reason = support_ref.0;
    solver.var_data[b.variable().index()].reason = clause_ref.0;

    let replaced =
        solver.replace_clause_with_final_hints(clause_idx, &[a.negated()], &[support_id]);
    assert!(
        matches!(replaced, ReplaceResult::Empty | ReplaceResult::Unit),
        "replacement should proceed far enough to rederive the removed reason"
    );

    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_text = String::from_utf8(writer.into_vec().expect("flush")).expect("utf8");
    let b_dimacs = b.to_dimacs().to_string();
    let unit_line = proof_text
        .lines()
        .find(|line| {
            let tokens: Vec<&str> = line.split_whitespace().collect();
            tokens.len() >= 3 && tokens[1] == b_dimacs && tokens[2] == "0"
        })
        .unwrap_or_else(|| panic!("expected derived unit line for {b:?}\nproof:\n{proof_text}"));
    let tokens: Vec<&str> = unit_line.split_whitespace().collect();
    let zero_idx = tokens
        .iter()
        .position(|&token| token == "0")
        .expect("LRAT line must contain literal terminator");
    let hints: Vec<u64> = tokens[zero_idx + 1..]
        .iter()
        .take_while(|&&token| token != "0")
        .map(|token| token.parse::<u64>().expect("hint must parse"))
        .collect();

    assert!(
        hints.contains(&old_clause_id),
        "derived unit must cite the old clause before it is deleted; line={unit_line}"
    );
}

#[test]
fn test_delete_clause_checked_long_clause_keeps_lazy_watch_cleanup() {
    let mut solver: Solver = Solver::new(3);
    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));
    let mut clause = vec![x0, x1, x2];
    let clause_ref = match solver.add_clause_watched(&mut clause) {
        AddResult::Added(clause_ref) => clause_ref,
        other => panic!("expected long clause to be Added, got {other:?}"),
    };

    let (watch0, watch1) = solver.arena.watched_literals(clause_ref.0 as usize);
    assert_eq!(count_clause_watches(&solver, watch0, clause_ref), 1);
    assert_eq!(count_clause_watches(&solver, watch1, clause_ref), 1);

    let deleted = solver.delete_clause_checked(clause_ref.0 as usize, ReasonPolicy::Skip);
    assert_eq!(deleted, DeleteResult::Deleted);
    assert!(
        !solver.arena.is_active(clause_ref.0 as usize),
        "long clause must be deleted"
    );
    assert_eq!(
        count_clause_watches(&solver, watch0, clause_ref),
        1,
        "long-clause delete keeps stale watcher until flush"
    );
    assert_eq!(
        count_clause_watches(&solver, watch1, clause_ref),
        1,
        "long-clause delete keeps stale watcher until flush"
    );

    solver.flush_watches();
    assert_eq!(count_clause_watches(&solver, watch0, clause_ref), 0);
    assert_eq!(count_clause_watches(&solver, watch1, clause_ref), 0);
}

#[test]
fn test_replace_clause_checked_lrat_hints_not_empty() {
    // 2 original clauses: [x0, x1, x2] and [¬x2].
    // The unit clause [¬x2] makes the strengthened clause [x0, x1]
    // RUP-derivable from the original formula (required by forward DRUP checker).
    let proof_manager = ProofOutput::lrat_text(Vec::new(), 2);
    let mut solver = Solver::with_proof_output(3, proof_manager);

    let x2_neg = Literal::negative(Variable(2));
    let _c0_off = solver.arena.len();
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ]);
    // Resolving clause: justifies removing x2 via RUP.
    let c1_off = solver.arena.len();
    solver.add_clause(vec![x2_neg]);
    // Set up level-0 trail state for x2 so the transitive reason collector
    // finds the unit clause reason and includes it in LRAT hints.
    solver.var_data[2].level = 0;
    solver.var_data[2].reason = c1_off as u32;
    solver.trail = vec![x2_neg];
    solver.vals[x2_neg.index()] = 1;
    solver.vals[x2_neg.negated().index()] = -1;
    let replace_result = solver.replace_clause_checked(
        0,
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
    );
    assert!(
        matches!(replace_result, ReplaceResult::Replaced),
        "clause strengthening should keep a non-unit clause"
    );

    let writer = solver.take_proof_writer().expect("proof writer");
    let proof = String::from_utf8(writer.into_vec().expect("flush")).expect("utf8");
    let add_line = proof
        .lines()
        .find(|line| !line.contains(" d "))
        .expect("expected LRAT addition line");
    let tokens: Vec<&str> = add_line.split_whitespace().collect();
    let zero_idx = tokens
        .iter()
        .position(|&t| t == "0")
        .expect("LRAT line must have literal terminator");
    let hint_count = tokens[zero_idx + 1..]
        .iter()
        .take_while(|&&t| t != "0")
        .count();
    assert!(
        hint_count > 0,
        "strengthening LRAT line should contain at least one hint: {add_line}"
    );
}

#[test]
fn test_replace_clause_checked_lrat_uses_removed_literal_negation_unit() {
    let proof_manager = ProofOutput::lrat_text(Vec::new(), 2);
    let mut solver = Solver::with_proof_output(2, proof_manager);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let nb = b.negated();

    let c0_off = solver.arena.len();
    solver.add_clause(vec![a, b]);
    let c1_off = solver.arena.len();
    solver.add_clause(vec![nb]);

    let old_clause_id = solver.clause_id(ClauseRef(c0_off as u32));
    let required_unit_id = solver.clause_id(ClauseRef(c1_off as u32));
    assert!(solver.process_initial_clauses().is_none());

    let replace_result = solver.replace_clause_checked(c0_off, &[a]);
    assert!(matches!(replace_result, ReplaceResult::Unit));

    let replacement_id = solver.clause_id(ClauseRef(c0_off as u32));
    let writer = solver.take_proof_writer().expect("proof writer");
    let proof = String::from_utf8(writer.into_vec().expect("flush")).expect("utf8");
    let add_line = proof
        .lines()
        .find(|line| line.starts_with(&format!("{replacement_id} ")))
        .expect("expected LRAT replacement add line");
    let tokens: Vec<&str> = add_line.split_whitespace().collect();
    let zero_idx = tokens
        .iter()
        .position(|&t| t == "0")
        .expect("LRAT line must contain literal terminator");
    let hints: Vec<u64> = tokens[zero_idx + 1..]
        .iter()
        .take_while(|&&t| t != "0")
        .map(|token| token.parse::<u64>().expect("hint must parse"))
        .collect();

    assert_eq!(
        hints,
        vec![old_clause_id, required_unit_id],
        "replacement must use proof of the removed literal's negation"
    );
}

#[test]
fn test_replace_clause_checked_lrat_skips_wrong_signed_removed_unit() {
    let proof_manager = ProofOutput::lrat_text(Vec::new(), 2);
    let mut solver = Solver::with_proof_output(2, proof_manager);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let nb = b.negated();

    let c0_off = solver.arena.len();
    solver.add_clause(vec![a, nb]);
    solver.add_clause(vec![nb]);

    let old_clause_id = solver.clause_id(ClauseRef(c0_off as u32));
    assert!(solver.process_initial_clauses().is_none());

    let replace_result = solver.replace_clause_checked(c0_off, &[a]);
    assert!(matches!(replace_result, ReplaceResult::Skipped));
    assert_eq!(
        solver.clause_id(ClauseRef(c0_off as u32)),
        old_clause_id,
        "skipped LRAT replacement must keep the original clause ID"
    );
    assert_eq!(solver.arena.literals(c0_off), &[a, nb]);
}

#[test]
fn test_replace_clause_checked_uses_captured_hints_when_reason_cleared() {
    let proof_manager = ProofOutput::lrat_text(Vec::new(), 3);
    let mut solver = Solver::with_proof_output(3, proof_manager);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));

    let c0_off = solver.arena.len();
    solver.add_clause(vec![a, b, c]); // target clause (ID 1)
    let c1_off = solver.arena.len();
    solver.add_clause(vec![a, b.negated()]); // reason clause for b=false (ID 2)
    solver.add_clause(vec![b, c]); // unrelated original clause (ID 3)

    let old_clause_id = solver.clause_id(ClauseRef(c0_off as u32));
    let reason_clause_id = solver.clause_id(ClauseRef(c1_off as u32));
    assert_eq!(old_clause_id, 1);
    assert_eq!(reason_clause_id, 2);

    // Simulate vivify behavior: reason existed at probe level, then backtrack cleared it.
    solver.var_data[b.variable().index()].reason = c1_off as u32;
    solver.var_data[b.variable().index()].reason = NO_REASON;

    let replace_result =
        solver.replace_clause_checked_with_lrat_hints(0, &[a, c], &[reason_clause_id]);
    assert!(
        matches!(replace_result, ReplaceResult::Replaced),
        "replacement should keep a non-unit clause"
    );

    let replaced_id = solver.clause_id(ClauseRef(0));
    let writer = solver.take_proof_writer().expect("proof writer");
    let proof = String::from_utf8(writer.into_vec().expect("flush")).expect("utf8");
    let add_line = proof
        .lines()
        .find(|line| line.starts_with(&format!("{replaced_id} ")))
        .expect("expected LRAT replacement add line");
    let tokens: Vec<&str> = add_line.split_whitespace().collect();
    let zero_idx = tokens
        .iter()
        .position(|&t| t == "0")
        .expect("LRAT line must contain literal terminator");
    let hints: Vec<u64> = tokens[zero_idx + 1..]
        .iter()
        .take_while(|&&t| t != "0")
        .map(|token| token.parse::<u64>().expect("hint must parse"))
        .collect();

    assert_eq!(
        hints,
        vec![old_clause_id, reason_clause_id],
        "after lrat_reverse_hints, old clause hint (single removal) comes first"
    );
}

#[test]
fn test_replace_clause_checked_resyncs_lrat_clause_id_for_followup_hints() {
    // 3 original clauses to make all derived clauses DRUP-valid:
    //   [x0, x1, x2]  — target for strengthening
    //   [¬x2]         — justifies removing x2 from target (RUP: ¬x0,¬x1 → x2 → conflict with ¬x2)
    //   [¬x1, x3]     — justifies learned [x0, x3] (RUP: ¬x0,¬x3 → x1 via [x0,x1] → conflict with [¬x1,x3])
    let proof_manager = ProofOutput::lrat_text(Vec::new(), 3);
    let mut solver = Solver::with_proof_output(4, proof_manager);

    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));
    let x3 = Literal::positive(Variable(3));

    // Three original clauses: LRAT IDs 1, 2, 3.
    solver.add_clause(vec![x0, x1, x2]);
    solver.add_clause(vec![x2.negated()]);
    solver.add_clause(vec![x1.negated(), x3]);
    let old_id = solver.clause_id(ClauseRef(0));
    assert_eq!(old_id, 1);
    assert_eq!(solver.cold.next_clause_id, 4);

    // Register helper clauses with the forward checker (debug-mode only)
    // so derived clauses pass the RUP check. Does not affect LRAT IDs.
    // ¬x2: makes strengthening [x0,x1,x2]→[x0,x1] RUP-valid.
    // x3:  makes learned clause [x0,x3] RUP-valid (negating x0,x3 →
    //      x3=false conflicts with [x3]).
    if let Some(ref mut pm) = solver.proof_manager {
        pm.register_original_clause(&[Literal::negative(Variable(2))]);
        pm.register_original_clause(&[x3]);
    }

    // Propagate level-0 unit clauses so the LRAT hint chain collector can
    // find reason chains for removed literals. Unit clauses (length 1) are
    // not watched by initialize_watches(); they must be propagated via
    // process_initial_clauses() which directly scans the arena (#5242).
    assert!(solver.process_initial_clauses().is_none());

    // Strengthen the original clause. This emits add + delete.
    let replace_result = solver.replace_clause_checked(0, &[x0, x1]);
    assert!(
        matches!(replace_result, ReplaceResult::Replaced),
        "strengthening should keep a non-unit clause"
    );

    let replaced_id = solver.clause_id(ClauseRef(0));
    assert!(
        replaced_id > old_id,
        "replaced clause must get a fresh LRAT ID (got {replaced_id}, old was {old_id})"
    );
    // next_clause_id is NOT advanced by replacement (#5239): replacement
    // clauses store their IDs in clause_ids[clause_idx] via the proof
    // writer, not through next_clause_id. Derived clauses added later
    // sync next_clause_id from the writer in add_learned_clause.

    // Learn a clause that references the replaced clause as a hint.
    // Full LRAT derivation chain for [x0, x3]:
    //   Negate: ¬x0, ¬x3
    //   Hint replaced_id [x0, x1]: ¬x0 falsifies x0, x1 unit → propagate x1
    //   Hint 3 [¬x1, x3]: x1 true, x3 false → conflict
    // The LRAT deletion step (for old clause 1) consumes one ID from the
    // shared monotonic space, so the learned clause gets replaced_id + 2.
    let learned_ref = solver.add_learned_clause(vec![x0, x3], 1, &[replaced_id, 3]);
    let learned_id = solver.clause_id(learned_ref);
    assert_eq!(
        learned_id,
        replaced_id + 2,
        "learned clause ID accounts for LRAT deletion step consuming one ID"
    );
    assert_eq!(solver.cold.next_clause_id, learned_id + 1);

    let writer = solver.take_proof_writer().expect("proof writer");
    let proof = String::from_utf8(writer.into_vec().expect("flush")).expect("utf8");
    let learned_line = proof
        .lines()
        .find(|line| line.starts_with(&format!("{learned_id} ")))
        .expect("expected learned clause LRAT addition line");

    let tokens: Vec<&str> = learned_line.split_whitespace().collect();
    let zero_idx = tokens
        .iter()
        .position(|&t| t == "0")
        .expect("LRAT line must contain literal terminator");
    let hints: Vec<u64> = tokens[zero_idx + 1..]
        .iter()
        .take_while(|&&t| t != "0")
        .map(|token| token.parse::<u64>().expect("hint must parse"))
        .collect();
    assert!(
        hints.contains(&replaced_id),
        "learned clause must reference replacement ID {replaced_id}, not stale deleted ID {old_id}: {hints:?}"
    );
    assert!(
        !hints.contains(&old_id),
        "learned clause must NOT reference deleted old ID {old_id}: {hints:?}"
    );
}

#[test]
fn test_replace_clause_checked_propagates_to_clause_trace() {
    use crate::ClauseTrace;

    let proof = ProofOutput::lrat_text(Vec::new(), 2);
    let mut solver = Solver::with_proof_output(3, proof);
    solver.cold.clause_trace = Some(ClauseTrace::new());

    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));

    // Original clause {x0, x1, x2} — LRAT ID 1
    let c0_off = solver.arena.len();
    solver.add_clause(vec![x0, x1, x2]);
    // Unit clause {¬x2} — LRAT ID 2 (makes {x0, x1} RUP-derivable)
    let c1_off = solver.arena.len();
    solver.add_clause(vec![x2.negated()]);

    let original_id = solver.clause_id(ClauseRef(c0_off as u32));
    let unit_id = solver.clause_id(ClauseRef(c1_off as u32));
    assert_eq!(original_id, 1);
    assert_eq!(unit_id, 2);

    // Strengthen clause 0 to {x0, x1}, providing ¬x2 clause as hint.
    // LRAT writer starts at ID 3 (after 2 originals).
    let result = solver.replace_clause_checked_with_lrat_hints(0, &[x0, x1], &[unit_id]);
    assert!(matches!(result, ReplaceResult::Replaced));

    let replacement_id = solver.clause_id(ClauseRef(0));
    assert_eq!(replacement_id, 3, "replaced clause gets fresh LRAT ID");

    let trace = solver.take_clause_trace().expect("clause trace enabled");

    // Trace: 2 originals (IDs 1, 2) + 1 replacement (ID 3)
    assert_eq!(
        trace.len(),
        3,
        "trace should have 2 originals + 1 replacement"
    );

    let replacement = trace
        .entries()
        .iter()
        .find(|e| e.id == replacement_id)
        .expect("replacement clause must appear in clause trace");

    assert!(
        !replacement.is_original,
        "replacement is derived, not original"
    );
    assert_eq!(replacement.clause.len(), 2, "replacement has 2 literals");
    assert!(
        !replacement.resolution_hints.is_empty(),
        "replacement must carry resolution hints for SMT proof reconstruction"
    );
}

#[test]
fn solver_namespace_is_bundled_at_clause_trace_extraction() {
    let mut solver = Solver::new(3);
    solver.enable_clause_trace();

    let snapshot = solver
        .snapshot_clause_trace()
        .expect("enabled trace has a snapshot");
    assert_eq!(snapshot.solver_num_vars(), Some(solver.total_num_vars()));
    assert_eq!(
        solver
            .clause_trace()
            .expect("live trace remains installed")
            .solver_num_vars(),
        None,
        "only extracted immutable snapshots carry namespace authority"
    );

    let expected = solver.total_num_vars();
    let taken = solver
        .take_clause_trace()
        .expect("enabled trace can be taken");
    assert_eq!(taken.solver_num_vars(), Some(expected));
}

#[test]
fn test_replace_clause_checked_vivify_lrat_standalone_validation() {
    let lrat_check = require_workspace_lrat_checker();

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));

    // 4 original clauses in CNF:
    // (a v b v c) ^ (!b) ^ (!c) ^ (!a)
    let proof_manager = ProofOutput::lrat_text(Vec::new(), 4);
    let mut solver = Solver::with_proof_output(3, proof_manager);
    solver.add_clause(vec![a, b, c]);
    solver.add_clause(vec![b.negated()]);
    solver.add_clause(vec![c.negated()]);

    assert!(solver.process_initial_clauses().is_none());
    solver.set_vivify_enabled(true);
    // Force irredundant vivification now; keep learned vivify out of the way.
    solver.inproc_ctrl.vivify.next_conflict = u64::MAX;
    solver.inproc_ctrl.vivify_irred.next_conflict = 0;
    solver.num_conflicts = 0;
    assert!(!solver.vivify(), "vivify should not derive UNSAT yet");
    assert!(
        solver.vivify_stats().clauses_examined > 0,
        "expected vivify to examine at least one clause"
    );

    let replaced_id = solver.clause_id(ClauseRef(0));
    assert!(
        replaced_id > 1,
        "vivify strengthening should assign a fresh clause ID"
    );

    // Add final contradictory unit.
    solver.add_clause(vec![a.negated()]);
    assert!(solver.solve().into_inner().is_unsat());

    let writer = solver.take_proof_writer().expect("proof writer");
    let proof = String::from_utf8(writer.into_vec().expect("flush")).expect("utf8");
    assert!(!proof.is_empty(), "proof must not be empty");

    let temp_dir = tempfile::tempdir().expect("create vivify LRAT validation tempdir");
    let cnf_path = temp_dir.path().join("vivify-replacement.cnf");
    let lrat_path = temp_dir.path().join("vivify-replacement.lrat");
    let cnf = "\
p cnf 3 4
1 2 3 0
-2 0
-3 0
-1 0
";
    std::fs::write(&cnf_path, cnf).expect("write CNF");
    std::fs::write(&lrat_path, &proof).expect("write LRAT");

    let output = lrat_check
        .command()
        .arg(&cnf_path)
        .arg(&lrat_path)
        .output()
        .expect("run exact-source standalone ay-lrat-check");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success() && !stdout.contains("FAILED") && !stderr.contains("FAILED"),
        "standalone ay-lrat-check rejected vivify replacement proof\nstdout: {stdout}\nstderr: {stderr}\nproof:\n{proof}"
    );
}

/// Regression test for #5014: replace_clause_checked must include
/// level0_proof_id in LRAT hints when reason was cleared by ClearLevel0.
///
/// Scenario: BVE deletes a unit clause via ClearLevel0, clearing
/// reason[vi] but preserving the clause's LRAT ID in level0_proof_id[vi].
/// A subsequent clause strengthening removes the literal propagated by
/// that deleted clause. The LRAT hint chain must still reference the
/// original clause ID through the level0_proof_id fallback.
#[test]
fn test_replace_clause_checked_level0_proof_id_fallback_after_clearlevel0() {
    // c0: [x0, x1, x2] — target clause (LRAT ID 1)
    // c1: [¬x2]        — unit clause (LRAT ID 2), propagates x2=false
    //
    // After propagation: x2=false at level 0, reason[2] = Some(ClauseRef(1))
    // Simulate ClearLevel0: reason[2] = None, level0_proof_id[2] = 2
    // Strengthen c0: [x0, x1, x2] → [x0, x1]
    //
    // Without the 3-tier fallback, hints miss clause 2, producing an
    // incomplete LRAT chain that lrat-check would reject.
    let proof_manager = ProofOutput::lrat_text(Vec::new(), 2);
    let mut solver = Solver::with_proof_output(3, proof_manager);

    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));
    let x2_neg = x2.negated();

    let _c0_off = solver.arena.len();
    solver.add_clause(vec![x0, x1, x2]); // LRAT ID 1
    let c1_off = solver.arena.len();
    solver.add_clause(vec![x2_neg]); // LRAT ID 2

    // Set up level-0 trail: x2=false propagated by c1.
    solver.var_data[2].level = 0;
    solver.trail = vec![x2_neg];
    solver.vals[x2_neg.index()] = 1;
    solver.vals[x2.index()] = -1;

    // Simulate ClearLevel0: BVE deletes c1, clearing the reason pointer
    // but preserving the LRAT clause ID for proof chain construction.
    let c1_id = solver.clause_id(ClauseRef(c1_off as u32));
    assert_ne!(c1_id, 0, "c1 must have a non-zero LRAT ID");
    solver.var_data[2].reason = NO_REASON;
    solver.record_level0_proof_id_for_lit(x2_neg, c1_id);

    // Strengthen target: [x0, x1, x2] → [x0, x1].
    let replace_result = solver.replace_clause_checked(0, &[x0, x1]);
    assert!(
        matches!(replace_result, ReplaceResult::Replaced),
        "strengthening should keep a non-unit clause"
    );

    // Parse LRAT output and verify c1's ID appears in hints.
    let writer = solver.take_proof_writer().expect("proof writer");
    let proof = String::from_utf8(writer.into_vec().expect("flush")).expect("utf8");
    let add_line = proof
        .lines()
        .find(|line| !line.contains(" d "))
        .expect("expected LRAT addition line");
    let tokens: Vec<&str> = add_line.split_whitespace().collect();
    let zero_idx = tokens
        .iter()
        .position(|&t| t == "0")
        .expect("LRAT line must have literal terminator");
    let hints: Vec<u64> = tokens[zero_idx + 1..]
        .iter()
        .take_while(|&&t| t != "0")
        .map(|token| token.parse::<u64>().expect("hint must parse"))
        .collect();

    assert!(
        hints.contains(&c1_id),
        "LRAT hints must include c1's ID ({c1_id}) via level0_proof_id fallback \
         (ClearLevel0 cleared reason[2] but saved proof ID). \
         Got hints: {hints:?}\nFull LRAT:\n{proof}"
    );
}

/// Regression test for #8222: add_clause_watched_impl must NOT check
/// lit_value for unit/conflict detection when watches_disconnected=true.
///
/// During BVE, watches are disconnected and prepare_watched_literals is
/// skipped. The first two literals of a resolvent are arbitrary — they may
/// both be false at level 0 while other literals are unassigned. Without
/// the fix, the solver would incorrectly derive an empty clause (spurious
/// UNSAT) from such a clause.
///
/// CaDiCaL (clause.cpp:643) asserts !watching() during elimination and
/// defers all conflict/unit detection to post-reconnection propagation.
#[test]
fn test_add_clause_watched_impl_no_spurious_conflict_when_watches_disconnected() {
    let mut solver: Solver = Solver::new(5);

    // Set up level-0 assignments: var0=false, var1=false. var2-4 unassigned.
    solver.var_data[0].level = 0;
    solver.vals[Literal::positive(Variable(0)).index()] = -1; // var0 = false
    solver.vals[Literal::negative(Variable(0)).index()] = 1;
    solver.trail.push(Literal::negative(Variable(0)));

    solver.var_data[1].level = 0;
    solver.vals[Literal::positive(Variable(1)).index()] = -1; // var1 = false
    solver.vals[Literal::negative(Variable(1)).index()] = 1;
    solver.trail.push(Literal::negative(Variable(1)));

    // Disconnect watches (simulating BVE mode).
    solver.watches.clear();
    solver.watches_disconnected = true;

    // Add a clause where the first two literals are false at level 0, but
    // the remaining literals are unassigned. This clause is NOT empty — it
    // has 3 satisfiable literals. But without the fix, the solver would
    // check lit_value(lits[0]) and lit_value(lits[1]), see both false, and
    // incorrectly derive an empty clause.
    let mut lits = vec![
        Literal::positive(Variable(0)), // false at level 0
        Literal::positive(Variable(1)), // false at level 0
        Literal::positive(Variable(2)), // unassigned
        Literal::positive(Variable(3)), // unassigned
        Literal::positive(Variable(4)), // unassigned
    ];
    let result = solver.add_clause_watched(&mut lits);
    assert!(
        matches!(result, AddResult::Added(_)),
        "clause with unassigned literals must be Added, not Empty; got {result:?}"
    );
    assert!(
        !solver.has_empty_clause,
        "solver must NOT derive empty clause when watched literals are \
         arbitrary (watches_disconnected=true)"
    );
}

/// Regression test for #8222: add_clause_watched_impl must NOT enqueue
/// a spurious unit when watches_disconnected=true.
///
/// When lits[0] is unassigned and lits[1] is false, the normal code path
/// would enqueue lits[0] as a unit. But with watches disconnected, lits[0]
/// and lits[1] are arbitrary — there may be other unassigned literals in
/// the clause, so it is NOT actually a unit.
#[test]
fn test_add_clause_watched_impl_no_spurious_unit_when_watches_disconnected() {
    let mut solver: Solver = Solver::new(4);

    // var0=unassigned, var1=false at level 0, var2=unassigned, var3=unassigned.
    solver.var_data[1].level = 0;
    solver.vals[Literal::positive(Variable(1)).index()] = -1;
    solver.vals[Literal::negative(Variable(1)).index()] = 1;
    solver.trail.push(Literal::negative(Variable(1)));

    solver.watches.clear();
    solver.watches_disconnected = true;

    let trail_before = solver.trail.len();

    // lits[0] is unassigned, lits[1] is false. Without the fix, this would
    // enqueue lits[0] as a unit propagation. But lits[2] and lits[3] are
    // also unassigned, so this is a normal clause, not a unit.
    let mut lits = vec![
        Literal::positive(Variable(0)), // unassigned
        Literal::positive(Variable(1)), // false at level 0
        Literal::positive(Variable(2)), // unassigned
        Literal::positive(Variable(3)), // unassigned
    ];
    let result = solver.add_clause_watched(&mut lits);
    assert!(
        matches!(result, AddResult::Added(_)),
        "multi-literal clause with watches disconnected must be Added, got {result:?}"
    );
    assert_eq!(
        solver.trail.len(),
        trail_before,
        "no literal should be enqueued when watches are disconnected \
         and clause has multiple unassigned literals"
    );
}

/// Regression test for #8222: unit clause detection still works correctly
/// when watches_disconnected=true. The else branch (lits.len()==1) checks
/// the actual single literal's value, which is always correct regardless
/// of watch state. This test verifies that genuine unit clauses are still
/// enqueued during BVE.
#[test]
fn test_add_clause_watched_impl_genuine_unit_still_works_when_watches_disconnected() {
    let mut solver: Solver = Solver::new(3);

    solver.watches.clear();
    solver.watches_disconnected = true;

    // Add a genuine unit clause.
    let mut lits = vec![Literal::positive(Variable(0))];
    let result = solver.add_clause_watched(&mut lits);
    assert!(
        matches!(result, AddResult::Unit(_)),
        "genuine unit clause must be detected as Unit even with watches disconnected; got {result:?}"
    );
    assert_eq!(
        solver.lit_value(Literal::positive(Variable(0))),
        Some(true),
        "unit literal must be enqueued (assigned true)"
    );
}

/// Regression test for #6270: deleting a level-0 reason clause must
/// materialize nested level-0 antecedents as derived units before using them
/// in the next derived unit step.
///
/// Chain:
///   c0: [x0]
///   c1: [¬x0, x1]
///   c2: [¬x1, x2]
///
/// Deleting c2 with ClearLevel0 derives [x2]. That derivation needs a unit
/// proof for x1, not the raw multi-literal clause c1. Prior code emitted c1
/// directly and the debug LRAT checker rejected the chain.
#[test]
fn test_delete_clause_checked_materializes_nested_level0_unit_proofs() {
    let proof = ProofOutput::lrat_text(Vec::new(), 3);
    let mut solver = Solver::with_proof_output(3, proof);

    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));

    let _c0_off = solver.arena.len();
    solver.add_clause(vec![x0]);
    let c1_off = solver.arena.len();
    solver.add_clause(vec![x0.negated(), x1]);
    let c2_off = solver.arena.len();
    solver.add_clause(vec![x1.negated(), x2]);

    assert!(
        solver.process_initial_clauses().is_none(),
        "unit propagation should not conflict"
    );
    solver.initialize_watches();
    assert!(
        solver.search_propagate().is_none(),
        "watch propagation should derive the nested level-0 chain"
    );
    assert_eq!(solver.lit_value(x0), Some(true));
    assert_eq!(solver.lit_value(x1), Some(true));
    assert_eq!(solver.lit_value(x2), Some(true));
    assert_eq!(solver.var_reason(1), Some(ClauseRef(c1_off as u32)));
    assert_eq!(solver.var_reason(2), Some(ClauseRef(c2_off as u32)));

    let c1_id = solver.clause_id(ClauseRef(c1_off as u32));
    let c2_id = solver.clause_id(ClauseRef(c2_off as u32));
    assert_ne!(c1_id, 0);
    assert_ne!(c2_id, 0);

    let deleted = solver.delete_clause_checked(c2_off, ReasonPolicy::ClearLevel0);
    assert!(
        matches!(deleted, DeleteResult::Deleted),
        "reason clause deletion should succeed"
    );
    assert_eq!(solver.var_data[2].reason, NO_REASON);
    assert_ne!(
        solver.cold.level0_proof_id[1], 0,
        "nested antecedent x1 must get a materialized unit proof ID"
    );
    assert_ne!(
        solver.cold.level0_proof_id[2], 0,
        "deleted reason target x2 must get a replacement unit proof ID"
    );
    assert_ne!(
        solver.cold.level0_proof_id[1], c1_id,
        "x1 must use a derived unit proof, not raw clause c1"
    );
    assert_ne!(
        solver.cold.level0_proof_id[2], c2_id,
        "x2 must use a derived unit proof, not raw clause c2"
    );
    let x1_unit_id = solver.cold.level0_proof_id[1];
    let x2_unit_id = solver.cold.level0_proof_id[2];
    assert!(
        solver.cold.lrat_delete_unit_hints_buf.is_empty(),
        "delete-unit LRAT scratch should be retained empty after emission"
    );
    assert!(
        solver.cold.lrat_delete_unit_hints_buf.capacity() >= 2,
        "delete-unit LRAT scratch should retain hint capacity"
    );

    let writer = solver.take_proof_writer().expect("proof writer");
    let proof = String::from_utf8(writer.into_vec().expect("flush")).expect("utf8");
    let x2_line = proof
        .lines()
        .find(|line| line.starts_with(&format!("{x2_unit_id} ")))
        .expect("expected derived x2 unit line");
    let tokens: Vec<&str> = x2_line.split_whitespace().collect();
    let zero_idx = tokens
        .iter()
        .position(|&token| token == "0")
        .expect("LRAT line must have literal terminator");
    let hints: Vec<u64> = tokens[zero_idx + 1..]
        .iter()
        .take_while(|&&token| token != "0")
        .map(|token| token.parse::<u64>().expect("hint must parse"))
        .collect();
    assert_eq!(
        hints,
        vec![x1_unit_id, c2_id],
        "delete-unit helper must preserve LRAT hint order: antecedent unit IDs first, deleted clause ID last\nproof:\n{proof}"
    );
}
