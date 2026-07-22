// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::literal::Literal;

#[test]
fn test_frozen_variable_survives_bve_round() {
    let mut solver = Solver::new(1);
    let v0 = Variable(0);

    let clause_idx = solver.add_clause_db(&[Literal::positive(v0)], false);
    solver.freeze(v0);

    let derived_unsat = solver.bve();
    assert!(!derived_unsat, "BVE should not derive UNSAT here");
    assert_eq!(
        solver.bve_stats().vars_eliminated,
        0,
        "BVE should not eliminate frozen variables"
    );
    assert!(!solver.inproc.bve.is_eliminated(v0));
    assert!(
        !solver.arena.is_empty_clause(clause_idx),
        "Frozen variable clause should remain after BVE"
    );
}

#[test]
fn test_unfrozen_variable_can_be_eliminated_by_bve() {
    // v0 has both positive and negative occurrences — BVE eliminates it by
    // resolving all positive clauses against negative clauses.
    let mut solver = Solver::new(3);
    let v0 = Variable(0);
    let v1 = Variable(1);
    let v2 = Variable(2);

    // (x0 | x1) and (!x0 | x2): v0 has both polarities, resolvent is (x1 | x2)
    let c0 = solver.add_clause_db(&[Literal::positive(v0), Literal::positive(v1)], false);
    let c1 = solver.add_clause_db(&[Literal::negative(v0), Literal::positive(v2)], false);

    // Freeze v1/v2 so pure elimination (#7004) doesn't destroy v0's clauses.
    solver.freeze(v1);
    solver.freeze(v2);

    let derived_unsat = solver.bve();
    assert!(!derived_unsat, "BVE should not derive UNSAT here");
    assert_eq!(
        solver.bve_stats().vars_eliminated,
        1,
        "BVE should eliminate v0 (both polarities present)"
    );
    assert!(solver.inproc.bve.is_eliminated(v0));
    assert!(
        solver.arena.is_empty_clause(c0),
        "Original clause should be deleted"
    );
    assert!(
        solver.arena.is_empty_clause(c1),
        "Original clause should be deleted"
    );
}

#[test]
fn test_bve_failed_candidate_still_consumes_effort_budget() {
    // x0 has 3 positive and 2 negative clauses. With growth_bound=0, bounded
    // elimination fails (up to 6 resolvents for 5 removed clauses), but the
    // effort counter must still advance for both candidate iteration and the
    // attempted resolution pairs.
    let mut solver = Solver::new(7);
    let x0 = Variable(0);
    let a = Variable(1);
    let b = Variable(2);
    let c = Variable(3);
    let d = Variable(4);
    let e = Variable(5);

    solver.add_clause_db(&[Literal::positive(x0), Literal::positive(a)], false);
    solver.add_clause_db(&[Literal::positive(x0), Literal::positive(b)], false);
    solver.add_clause_db(&[Literal::positive(x0), Literal::positive(c)], false);
    solver.add_clause_db(&[Literal::negative(x0), Literal::positive(d)], false);
    solver.add_clause_db(&[Literal::negative(x0), Literal::positive(e)], false);

    // Freeze pure auxiliary variables so they aren't eliminated before x0.
    // With pure elimination enabled (#7004), a-e would otherwise be
    // eliminated first (score 0 < x0's score 6), destroying x0's clauses.
    solver.freeze(a);
    solver.freeze(b);
    solver.freeze(c);
    solver.freeze(d);
    solver.freeze(e);

    assert_eq!(
        solver.cold.bve_resolutions, 0,
        "new solver should start with zero BVE effort"
    );
    let derived_unsat = solver.bve();
    assert!(
        !derived_unsat,
        "BVE should not derive UNSAT on this formula"
    );
    assert_eq!(
        solver.bve_stats().vars_eliminated,
        0,
        "x0 should fail bounded elimination with growth_bound=0"
    );
    assert_eq!(
        solver.cold.bve_resolutions, 6,
        "failed elimination must charge 3x2 attempted resolution pairs"
    );
}

#[test]
fn test_bve_effective_binary_gate_detection_uses_vals() {
    // Construct an AND gate y = (a ∧ b) where one side-clause is only
    // usable after filtering a currently-false literal.
    //
    // Defining clauses:
    //   (~y ∨ a ∨ j1)       [effective binary when j1 is false]
    //   (~y ∨ b)
    //   (y ∨ ~a ∨ ~b)       [clean base clause]
    //
    // Note (#8477): The original test also had a root-false literal j2 in
    // the base clause, but without a corresponding side clause that is
    // unsound -- it produces an incomplete gate that misses a constraint
    // needed for equisatisfiability during BVE. The fix in #8477 rejects
    // such incomplete gates. This test now uses a clean base clause to
    // isolate the effective-binary side-clause detection.
    //
    // Additional non-gate clauses are present to exercise the full pipeline.
    // The solver's BVE uses value-aware gate detection to identify the gate
    // and eliminate y despite the non-gate clauses.
    let mut solver = Solver::new(9);

    let y = Variable(0);
    let a = Variable(1);
    let b = Variable(2);
    let j1 = Variable(3);
    let _j2 = Variable(4);
    let p1 = Variable(5);
    let p2 = Variable(6);
    let n1 = Variable(7);
    let m1 = Variable(8);

    solver.add_clause_db(
        &[
            Literal::negative(y),
            Literal::positive(a),
            Literal::positive(j1),
        ],
        false,
    );
    solver.add_clause_db(&[Literal::negative(y), Literal::positive(b)], false);
    solver.add_clause_db(
        &[
            Literal::positive(y),
            Literal::negative(a),
            Literal::negative(b),
        ],
        false,
    );

    // Non-gate positive occurrences of y.
    solver.add_clause_db(&[Literal::positive(y), Literal::positive(p1)], false);
    solver.add_clause_db(&[Literal::positive(y), Literal::positive(p2)], false);

    // Non-gate negative occurrences of y.
    solver.add_clause_db(
        &[
            Literal::negative(y),
            Literal::positive(n1),
            Literal::positive(m1),
        ],
        false,
    );

    // Padding clauses (not involving y) to raise active_clause_count above
    // the 10% growth guard in eliminate.rs (growth*10 > active_before).
    // Without subsumption dropping resolvents (#7916), BVE may produce 1
    // extra resolvent beyond clauses_removed, triggering the guard on small
    // formulas. 10 padding clauses ensures active_count >= 16 so growth=1
    // stays below 10%.
    for i in 0..10u32 {
        solver.add_clause_db(
            &[
                Literal::positive(Variable(1 + (i % 2))),
                Literal::negative(Variable(5 + (i % 4))),
            ],
            false,
        );
    }

    // Fix j1=false at level 0 so the side clause becomes effectively binary.
    solver.enqueue(Literal::negative(j1), None);

    // Freeze all non-pivot variables so BVE focuses on eliminating y.
    for var in [a, b, j1, _j2, p1, p2, n1, m1] {
        solver.freeze(var);
    }

    let mut baseline_bve = BVE::new(9);
    baseline_bve.rebuild(&solver.arena);

    let pos_occs = baseline_bve.get_occs(Literal::positive(y)).to_vec();
    let neg_occs = baseline_bve.get_occs(Literal::negative(y)).to_vec();

    let mut extractor = GateExtractor::new(9);
    assert!(
        extractor
            .find_gate_for_bve_with_vals(y, &solver.arena, &pos_occs, &neg_occs, &[])
            .is_none(),
        "syntactic gate detection should fail before value filtering",
    );

    let gate = extractor
        .find_gate_for_bve_with_vals(y, &solver.arena, &pos_occs, &neg_occs, &solver.vals)
        .expect("value-aware gate detection should recover the AND gate");
    assert!(
        !gate.defining_clauses.is_empty(),
        "value-aware gate should identify defining clauses",
    );

    // After #5661, restricted resolution includes non-gate × non-gate pairs.
    // Forward subsumption of resolvents during BVE was removed (#7916,
    // braun.7 FINALIZE_SAT_FAIL) so all resolvents are now kept. Without
    // subsumption dropping resolvents, gated BVE may produce more resolvents
    // than clauses removed, which exceeds fastelim's cap. Use additive mode
    // with growth_bound=2 (budget = clauses_removed + 2 = 8, comfortably
    // accommodating 7 non-tautological resolvents).
    solver.inproc.bve.increment_growth_bound(); // 0 → 1
    solver.inproc.bve.increment_growth_bound(); // 1 → 2
    let derived_unsat = solver.bve();
    assert!(
        !derived_unsat,
        "BVE should not derive UNSAT in the effective-binary gate scenario",
    );
    assert!(
        solver.inproc.bve.is_eliminated(y),
        "solver BVE path should eliminate y using value-aware gate detection",
    );
    assert!(
        solver.gate_stats().and_gates >= 1,
        "solver should record at least one detected AND gate during BVE",
    );
}

#[test]
fn test_bve_semantic_definition_learns_failed_literal() {
    let mut solver = Solver::new(3);
    let x = Variable(0);
    let a = Variable(1);
    let b = Variable(2);

    solver.add_clause_db(&[Literal::positive(x), Literal::positive(a)], false);
    solver.add_clause_db(&[Literal::positive(x), Literal::negative(a)], false);
    solver.add_clause_db(&[Literal::negative(x), Literal::positive(b)], false);

    solver.freeze(a);
    solver.freeze(b);

    let derived_unsat = solver.bve();
    assert!(
        !derived_unsat,
        "semantic definition extraction should learn a unit, not UNSAT",
    );
    assert_eq!(
        solver.lit_val(Literal::positive(x)),
        1,
        "one-sided semantic core should force x=true",
    );
    assert!(
        !solver.inproc.bve.is_eliminated(x),
        "failed-literal extraction should not eliminate the pivot in the same pass",
    );
}

#[test]
fn test_otfs_strengthen_lrat_hint_references_replaced_clause() {
    // OTFS is disabled in LRAT mode because OTFS emits TrustedTransform
    // which LRAT verification rejects. Verify that otfs_strengthen
    // correctly returns false in LRAT mode.
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 1);
    let mut solver: Solver = Solver::with_proof_output(4, proof);
    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));
    let x3 = Literal::positive(Variable(3));

    assert!(solver.add_clause(vec![x0, x1, x2, x3]));
    solver.initialize_watches();

    let clause_ref = ClauseRef(0);
    let old_clause_id = solver.clause_id(clause_ref);
    assert_ne!(
        old_clause_id, 0,
        "OTFS regression test requires clause to have LRAT ID"
    );

    // New OTFS semantics: pivot = propagated literal, all others false.
    solver.decide(x0.negated()); // x0 = false at level 1
    let _ = solver.propagate();
    solver.decide(x1); // x1 = true at level 2 (propagated/pivot)
    let _ = solver.propagate();
    solver.decide(x2.negated()); // x2 = false at level 3
    let _ = solver.propagate();
    solver.decide(x3.negated()); // x3 = false at level 4
    let _ = solver.propagate();

    // OTFS is disabled in LRAT mode: must return false
    assert!(
        !solver.otfs_strengthen(clause_ref, x1),
        "OTFS must be disabled in LRAT mode (TrustedTransform not valid for LRAT)"
    );

    // Clause should be unchanged
    assert_eq!(
        solver.clause_id(clause_ref),
        old_clause_id,
        "clause ID must not change when OTFS is disabled"
    );
}
