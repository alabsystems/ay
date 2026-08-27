// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Test for #1581: Subsumption code path handles unit/empty clauses correctly.
///
/// This test verifies that when subsumption/strengthening produces unit or
/// empty clauses, the solver correctly handles them (propagate units,
/// mark UNSAT for empty).
///
/// Note: Current self-subsumption requires D.len > C.len, so strengthening
/// to unit requires C to be unit and D to be binary. But unit subsumers are
/// skipped (C.len >= 2 required). This means the unit/empty handling in
/// subsume() is defensive code for future changes or other code paths.
///
/// This test exercises the broader system to ensure soundness:
/// - Self-subsumption: C={0,1}, D={¬0,1,2} → D becomes {1,2}
/// - Combined with unit propagation, this should derive UNSAT.
#[test]
fn test_subsumption_strengthening_with_propagation() {
    // Variables: x0, x1, x2
    let mut solver = Solver::new(3);
    let x0 = Variable(0);
    let x1 = Variable(1);
    let x2 = Variable(2);

    // Original unit clause: x0 is true
    solver.add_clause(vec![Literal::positive(x0)]);

    // Original: ¬x1 ∨ ¬x2 (at least one is false)
    solver.add_clause(vec![Literal::negative(x1), Literal::negative(x2)]);

    // Learned clause C = {x0, x1} (binary)
    // This is the subsumer
    solver.add_clause_db(&[Literal::positive(x0), Literal::positive(x1)], true);

    // Learned clause D = {¬x0, x1, x2} (ternary)
    // After self-subsumption with C (removing ¬x0): D becomes {x1, x2}
    // Combined with {¬x1 ∨ ¬x2}, this forces a choice
    solver.add_clause_db(
        &[
            Literal::negative(x0),
            Literal::positive(x1),
            Literal::positive(x2),
        ],
        true,
    );

    // Original unit clauses to force UNSAT through subsumption path
    // {x1} and {x2} force both true, but {¬x1 ∨ ¬x2} requires one false.
    // These must be irredundant (original) — learned clauses can be deleted.
    solver.add_clause(vec![Literal::positive(x1)]);
    solver.add_clause(vec![Literal::positive(x2)]);

    // The formula is UNSAT:
    // - {x0} forces x0=true
    // - {x1} forces x1=true
    // - {x2} forces x2=true
    // - {¬x1 ∨ ¬x2} requires x1=false OR x2=false
    // Contradiction!

    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "Expected UNSAT but got {result:?}"
    );
}

/// Test for #1581: Self-subsumption strengthening reduces clause size.
///
/// Verify that self-subsumption works: C={a,b} and D={¬a,b,c} → D becomes {b,c}
#[test]
fn test_subsumption_self_strengthening_basic() {
    // Variables: a, b, c
    let mut solver = Solver::new(3);
    let a = Variable(0);
    let b = Variable(1);
    let c = Variable(2);

    // Learned clause C = {a, b} (binary subsumer)
    solver.add_clause_db(&[Literal::positive(a), Literal::positive(b)], true);

    // Learned clause D = {¬a, b, c} (ternary, can be strengthened)
    // Self-subsumption removes ¬a, leaving {b, c}
    let d_off = solver.arena.len();
    solver.add_clause_db(
        &[
            Literal::negative(a),
            Literal::positive(b),
            Literal::positive(c),
        ],
        true,
    );

    // Build occurrence lists
    solver.inproc.subsumer.rebuild(&solver.arena);

    // Run subsumption
    let freeze_counts = vec![0u32; 3];
    let result = solver
        .inproc
        .subsumer
        .run_subsumption(&mut solver.arena, &freeze_counts, 0, 100);

    // D (at word offset d_off) should be strengthened
    let strengthened = result.strengthened.iter().find(|(idx, _, _)| *idx == d_off);
    let (_, new_lits, _) =
        strengthened.expect("Clause D should be strengthened by self-subsumption");
    assert_eq!(new_lits.len(), 2, "Strengthened clause should be binary");
    assert!(
        new_lits.contains(&Literal::positive(b)),
        "Should contain +b"
    );
    assert!(
        new_lits.contains(&Literal::positive(c)),
        "Should contain +c"
    );
    assert!(
        !new_lits.contains(&Literal::negative(a)),
        "Should NOT contain -a"
    );
}

/// Test for #1581: unit subsumers can strengthen binary clauses to units.
#[test]
fn test_unit_clause_strengthens_binary() {
    let mut solver = Solver::new(2);
    let a = Variable(0);
    let b = Variable(1);

    // Unit learned clause C = {a}
    solver.add_clause_db(&[Literal::positive(a)], true);

    // Binary learned clause D = {¬a, b}
    solver.add_clause_db(&[Literal::negative(a), Literal::positive(b)], true);

    solver.inproc.subsumer.rebuild(&solver.arena);

    let freeze_counts = vec![0u32; 2];
    let result = solver
        .inproc
        .subsumer
        .run_subsumption(&mut solver.arena, &freeze_counts, 0, 100);

    let strengthened = result
        .strengthened
        .iter()
        .find(|(_, new_lits, _)| new_lits.as_slice() == [Literal::positive(b)])
        .expect("Binary clause should be strengthened by unit subsumer");
    assert_eq!(strengthened.1, vec![Literal::positive(b)]);
}

/// Test for #1581: opposing unit strengthening to empty marks UNSAT.
#[test]
fn test_unit_clause_strengthening_to_empty_marks_unsat() {
    let mut solver = Solver::new(1);
    let a = Variable(0);

    solver.add_clause_db(&[Literal::positive(a)], false);
    solver.add_clause_db(&[Literal::negative(a)], false);

    solver.subsume();

    assert!(
        solver.has_empty_clause,
        "opposing unit clauses should make subsume() mark UNSAT"
    );
}

/// Test for #1581: Unit strengthening that contradicts assignment marks UNSAT.
///
/// The forward subsumption engine (CaDiCaL-style) skips clauses with level-0
/// assigned literals, delegating contradiction detection to BCP. This test
/// verifies the end-to-end path: subsumption + BCP detects the contradiction.
#[test]
fn test_unit_strengthening_contradiction_detected() {
    // Variables: a, b
    let mut solver = Solver::new(2);
    let a = Variable(0);
    let b = Variable(1);

    // Clauses: ¬b, a, ¬a ∨ b → UNSAT (b must be both true and false)
    solver.add_clause(vec![Literal::negative(b)]);
    solver.add_clause(vec![Literal::positive(a)]);
    solver.add_clause(vec![Literal::negative(a), Literal::positive(b)]);

    // Full solve should return UNSAT
    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "Expected UNSAT but got {result:?}"
    );
}

/// Build `C = {a,b,c,d}` forward-subsumed by `D = {a,b}`, ready for `subsume()`.
/// Returns `(solver, subsumed_idx)`.
fn forward_subsumption_fixture() -> (Solver, usize) {
    let mut solver = Solver::new(4);
    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));
    let d = Literal::positive(Variable(3));

    let subsumed_idx = solver.add_clause_db(&[a, b, c, d], false);
    let _subsumer_idx = solver.add_clause_db(&[a, b], false);
    solver.initialize_watches();
    for v in solver.subsume_dirty.iter_mut() {
        *v = true;
    }
    (solver, subsumed_idx)
}

/// A forward-subsumed clause that a queued theory conflict still owns must be
/// RETAINED, and retaining it must not trip the subsumption post-condition.
///
/// The post-condition used to assert `is_reason_clause_marked` on every
/// retained clause, exempting only the #6913 dead-subsumer case. A clause in
/// `pending_theory_conflicts` is refused by `can_delete_clause` (the queue owns
/// the `ClauseRef` until the solve loop consumes it, #6262) while being no
/// var's reason, so it satisfied neither the assertion nor its exemptions and
/// panicked a debug build mid-solve — with `BUG: subsume() left clause N active
/// without reason protection`, which reads like a subsumption defect but is a
/// correct, required retention.
#[test]
fn test_subsume_retains_queued_theory_conflict_without_tripping_postcondition() {
    let (mut solver, subsumed_idx) = forward_subsumption_fixture();

    solver
        .pending_theory_conflicts
        .push_back(ClauseRef(subsumed_idx as u32));

    // The discriminator that decides "over-strong assert" vs "real subsume
    // bug": the retained clause is not a reason for any assigned literal, so
    // the old assertion's premise — not the algorithm — was what was wrong.
    assert!(solver.trail.is_empty());
    assert!(!solver.is_reason_clause_marked(subsumed_idx));
    assert_eq!(
        solver.classify_forward_subsumption_retention(subsumed_idx),
        mutate::ForwardSubsumptionRetention::TheoryQueued,
    );

    solver.subsume();

    assert!(
        solver.arena.is_active(subsumed_idx) && !solver.arena.is_dead(subsumed_idx),
        "a queued theory conflict's clause must survive subsumption — deleting it \
         leaves take_pending_theory_conflict dereferencing a dead clause",
    );
}

/// Narrowness pin for the retention tripwire: the classification must report
/// `Unexplained` for a clause the pipeline has no reason to keep. Without this,
/// widening the exemption set to silence the panic could quietly turn the
/// tripwire into a constant `true`.
#[test]
fn test_forward_subsumption_retention_classifies_unexplained() {
    let (solver, subsumed_idx) = forward_subsumption_fixture();

    // Deletable clause: not a reason, not queued, LRAT off. Nothing explains
    // keeping it, so a decline here would be a genuine pipeline bug.
    assert!(solver.can_delete_clause(subsumed_idx, mutate::ReasonPolicy::Skip));
    assert!(!solver.cold.lrat_enabled);
    assert_eq!(
        solver.classify_forward_subsumption_retention(subsumed_idx),
        mutate::ForwardSubsumptionRetention::Unexplained,
    );
}

/// The historical case the post-condition was written for still classifies as
/// reason protection rather than falling through to the tripwire.
#[test]
fn test_forward_subsumption_retention_classifies_reason_protected() {
    let (mut solver, subsumed_idx) = forward_subsumption_fixture();

    // Make the clause the reason for a level-0 assignment.
    let a = Literal::positive(Variable(0));
    solver.enqueue(a, Some(ClauseRef(subsumed_idx as u32)));
    solver.invalidate_reason_clause_marks();
    solver.ensure_reason_clause_marks_current();

    assert!(solver.is_reason_clause_marked(subsumed_idx));
    assert_eq!(
        solver.classify_forward_subsumption_retention(subsumed_idx),
        mutate::ForwardSubsumptionRetention::ReasonProtected,
    );
}

/// With LRAT on, a decline that `can_delete_clause` does not object to is the
/// proof-bookkeeping case and must NOT trip the tripwire. This is the shape
/// reachable under a solve deadline: `materialize_level0_unit_proofs_impl`
/// honours the stop between proof rows and returns false, so
/// `delete_clause_checked` reports `Skipped` for a clause that is neither a
/// reason nor theory-queued.
#[test]
fn test_forward_subsumption_retention_classifies_proof_bookkeeping() {
    let (mut solver, subsumed_idx) = forward_subsumption_fixture();
    solver.cold.lrat_enabled = true;

    assert!(solver.can_delete_clause(subsumed_idx, mutate::ReasonPolicy::Skip));
    assert_eq!(
        solver.classify_forward_subsumption_retention(subsumed_idx),
        mutate::ForwardSubsumptionRetention::ProofBookkeeping,
    );
}
