// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_solve_with_proof_tracking_reapplies_phase_hints_after_conflict_6296() {
    let phase_calls = Rc::new(Cell::new(0));
    let phase_atom = TermId::new(26);
    let blocker_atom = TermId::new(27);
    let theory = ReapplyingPhaseHintTheory::new(phase_atom, blocker_atom, Rc::clone(&phase_calls));
    let mut dpll = DpllT::new(3, theory);
    configure_phase_hint_test_solver(&mut dpll);
    dpll.register_theory_atom(phase_atom, 0);
    dpll.register_theory_atom(blocker_atom, 1);
    dpll.add_clause(vec![Literal::positive(Variable::new(2))]);

    let mut tracker = proof_tracker::ProofTracker::new();
    tracker.enable();
    let negations = HashMap::default();

    let result = dpll.solve_with_proof_tracking(&mut tracker, &negations);
    assert!(
        matches!(result, Ok(SatResult::Sat(_))),
        "proof-tracking solve should re-apply updated phase hints after a theory conflict, got {result:?}"
    );
    let model = match result {
        Ok(SatResult::Sat(model)) => model,
        _ => Vec::new(),
    };
    assert_eq!(
        model,
        vec![true, false, true],
        "proof-tracking solve should honor the updated second-round theory hint",
    );
    assert!(
        phase_calls.get() > 2,
        "proof-tracking solve should re-consult theory phase hints after the first conflict"
    );
}

#[test]
fn test_assumption_proof_tracking_reapplies_phase_hints_after_conflict_6296() {
    let phase_calls = Rc::new(Cell::new(0));
    let phase_atom = TermId::new(28);
    let blocker_atom = TermId::new(29);
    let theory = ReapplyingPhaseHintTheory::new(phase_atom, blocker_atom, Rc::clone(&phase_calls));
    let mut dpll = DpllT::new(4, theory);
    configure_phase_hint_test_solver(&mut dpll);
    dpll.register_theory_atom(phase_atom, 0);
    dpll.register_theory_atom(blocker_atom, 1);
    dpll.add_clause(vec![Literal::positive(Variable::new(2))]);

    let mut tracker = proof_tracker::ProofTracker::new();
    tracker.enable();
    let negations = HashMap::default();

    let result = dpll.solve_with_assumptions_and_proof_tracking(
        &[Literal::positive(Variable::new(3))],
        &mut tracker,
        &negations,
    );
    assert!(
        matches!(result, Ok(AssumeResult::Sat(_)) | Ok(AssumeResult::Unknown)),
        "proof-tracking assumption solve should re-apply updated phase hints after a theory conflict or return unknown, got {result:?}"
    );
    let model = match result {
        Ok(AssumeResult::Sat(model)) => model,
        Ok(AssumeResult::Unknown) => return,
        _ => Vec::new(),
    };
    assert_eq!(
        model,
        vec![true, false, true, true],
        "proof-tracking assumption solve should honor the updated second-round theory hint",
    );
    assert!(
        phase_calls.get() >= 4,
        "proof-tracking assumption solve should consult both theory atoms again after the first conflict"
    );
}
