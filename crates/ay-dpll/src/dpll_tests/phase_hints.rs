// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression coverage for DPLL(T) phase-hint plumbing (#6296).

use super::*;
use std::cell::Cell;
use std::rc::Rc;

mod proof_tracking_reruns;

struct CountingPhaseHintTheory {
    phase_atom: TermId,
    phase_calls: Rc<Cell<usize>>,
}

impl CountingPhaseHintTheory {
    fn new(phase_atom: TermId, phase_calls: Rc<Cell<usize>>) -> Self {
        Self {
            phase_atom,
            phase_calls,
        }
    }
}

impl TheorySolver for CountingPhaseHintTheory {
    fn assert_literal(&mut self, _literal: TermId, _value: bool) {}

    fn check(&mut self) -> TheoryResult {
        TheoryResult::Sat
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        vec![]
    }

    fn push(&mut self) {}

    fn pop(&mut self) {}

    fn reset(&mut self) {}

    fn suggest_phase(&self, atom: TermId) -> Option<bool> {
        if atom == self.phase_atom {
            self.phase_calls.set(self.phase_calls.get() + 1);
            Some(false)
        } else {
            None
        }
    }
}

struct ReapplyingPhaseHintTheory {
    phase_atom: TermId,
    blocker_atom: TermId,
    phase_calls: Rc<Cell<usize>>,
    phase_atom_hint: Cell<bool>,
    assignments: HashMap<TermId, bool>,
    scopes: Vec<HashMap<TermId, bool>>,
    checks: usize,
}

impl ReapplyingPhaseHintTheory {
    fn new(phase_atom: TermId, blocker_atom: TermId, phase_calls: Rc<Cell<usize>>) -> Self {
        Self {
            phase_atom,
            blocker_atom,
            phase_calls,
            phase_atom_hint: Cell::new(false),
            assignments: HashMap::default(),
            scopes: Vec::new(),
            checks: 0,
        }
    }
}

impl TheorySolver for ReapplyingPhaseHintTheory {
    fn assert_literal(&mut self, literal: TermId, value: bool) {
        self.assignments.insert(literal, value);
    }

    fn check(&mut self) -> TheoryResult {
        self.checks += 1;
        if self.checks == 1 {
            self.phase_atom_hint.set(true);
            return TheoryResult::Unsat(vec![TheoryLit {
                term: self.blocker_atom,
                value: true,
            }]);
        }

        if self.assignments.get(&self.phase_atom).copied() == Some(true)
            && self.assignments.get(&self.blocker_atom).copied() == Some(false)
        {
            TheoryResult::Sat
        } else {
            TheoryResult::Unknown
        }
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        vec![]
    }

    fn push(&mut self) {
        self.scopes.push(self.assignments.clone());
    }

    fn pop(&mut self) {
        self.assignments = self.scopes.pop().unwrap_or_default();
    }

    fn reset(&mut self) {
        self.assignments.clear();
        self.scopes.clear();
        self.checks = 0;
        self.phase_atom_hint.set(false);
    }

    fn suggest_phase(&self, atom: TermId) -> Option<bool> {
        if atom == self.phase_atom {
            self.phase_calls.set(self.phase_calls.get() + 1);
            Some(self.phase_atom_hint.get())
        } else if atom == self.blocker_atom {
            self.phase_calls.set(self.phase_calls.get() + 1);
            Some(true)
        } else {
            None
        }
    }
}

fn configure_phase_hint_test_solver<T: TheorySolver>(dpll: &mut DpllT<'_, T>) {
    dpll.sat_solver_mut().set_preprocess_enabled(false);
    dpll.sat_solver_mut().set_walk_enabled(false);
    dpll.sat_solver_mut().set_warmup_enabled(false);
}

#[test]
fn test_interruptible_step_uses_phase_hints_6296() {
    let phase_calls = Rc::new(Cell::new(0));
    let phase_atom = TermId::new(10);
    let theory = CountingPhaseHintTheory::new(phase_atom, Rc::clone(&phase_calls));
    let mut dpll = DpllT::new(2, theory);
    configure_phase_hint_test_solver(&mut dpll);
    dpll.register_theory_atom(phase_atom, 0);
    dpll.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);

    let result = dpll.solve_step_interruptible(|| false);
    assert!(
        matches!(result, Ok(SolveStepResult::Done(SatResult::Sat(_)))),
        "expected SAT from interruptible step, got {result:?}"
    );
    let model = match result {
        Ok(SolveStepResult::Done(SatResult::Sat(model))) => model,
        _ => Vec::new(),
    };
    assert_eq!(
        model,
        vec![false, true],
        "interruptible step should use suggest_phase(false) for the theory atom",
    );

    assert!(
        phase_calls.get() > 0,
        "interruptible step must consult suggest_phase for theory atoms"
    );
}

#[test]
fn test_solve_with_assumptions_uses_phase_hints_6296() {
    let phase_calls = Rc::new(Cell::new(0));
    let phase_atom = TermId::new(11);
    let theory = CountingPhaseHintTheory::new(phase_atom, Rc::clone(&phase_calls));
    let mut dpll = DpllT::new(3, theory);
    configure_phase_hint_test_solver(&mut dpll);
    dpll.register_theory_atom(phase_atom, 0);
    dpll.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);

    let result = dpll.solve_with_assumptions(&[Literal::positive(Variable::new(2))]);
    assert!(
        matches!(result, Ok(AssumeResult::Sat(_))),
        "expected SAT from assumption solve, got {result:?}"
    );
    let model = match result {
        Ok(AssumeResult::Sat(model)) => model,
        _ => Vec::new(),
    };
    assert_eq!(
        model,
        vec![false, true, true],
        "assumption solve should keep the theory atom on the hinted false phase",
    );

    assert!(
        phase_calls.get() > 0,
        "assumption solve must consult suggest_phase for theory atoms"
    );
    assert_eq!(
        dpll.sat_solver().var_phase(Variable::new(0)),
        Some(false),
        "assumption solve should pre-apply the theory hint to SAT saved phases"
    );
}

#[test]
fn test_solve_with_proof_tracking_uses_phase_hints_6296() {
    let phase_calls = Rc::new(Cell::new(0));
    let phase_atom = TermId::new(13);
    let theory = CountingPhaseHintTheory::new(phase_atom, Rc::clone(&phase_calls));
    let mut dpll = DpllT::new(2, theory);
    configure_phase_hint_test_solver(&mut dpll);
    dpll.register_theory_atom(phase_atom, 0);
    dpll.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);

    let mut tracker = proof_tracker::ProofTracker::new();
    tracker.enable();
    let negations = HashMap::default();

    let result = dpll.solve_with_proof_tracking(&mut tracker, &negations);
    assert!(
        matches!(result, Ok(SatResult::Sat(_))),
        "expected SAT from proof-tracking solve, got {result:?}"
    );
    let model = match result {
        Ok(SatResult::Sat(model)) => model,
        _ => Vec::new(),
    };
    assert_eq!(
        model,
        vec![false, true],
        "proof-tracking solve should preserve the hinted false phase",
    );

    assert!(
        phase_calls.get() > 0,
        "proof-tracking solve must consult suggest_phase for theory atoms"
    );
    assert_eq!(
        dpll.sat_solver().var_phase(Variable::new(0)),
        Some(false),
        "proof-tracking solve should pre-apply the theory hint to SAT saved phases"
    );
}

#[test]
fn test_assumption_proof_tracking_uses_phase_hints_6296() {
    let phase_calls = Rc::new(Cell::new(0));
    let phase_atom = TermId::new(14);
    let theory = CountingPhaseHintTheory::new(phase_atom, Rc::clone(&phase_calls));
    let mut dpll = DpllT::new(3, theory);
    configure_phase_hint_test_solver(&mut dpll);
    dpll.register_theory_atom(phase_atom, 0);
    dpll.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);

    let mut tracker = proof_tracker::ProofTracker::new();
    tracker.enable();
    let negations = HashMap::default();

    let result = dpll.solve_with_assumptions_and_proof_tracking(
        &[Literal::positive(Variable::new(2))],
        &mut tracker,
        &negations,
    );
    assert!(
        matches!(result, Ok(AssumeResult::Sat(_))),
        "expected SAT from proof-tracking assumption solve, got {result:?}"
    );
    let model = match result {
        Ok(AssumeResult::Sat(model)) => model,
        _ => Vec::new(),
    };
    assert_eq!(
        model,
        vec![false, true, true],
        "proof-tracking assumption solve should keep the theory atom on the hinted false phase",
    );

    assert!(
        phase_calls.get() > 0,
        "proof-tracking assumption solve must consult suggest_phase for theory atoms"
    );
    assert_eq!(
        dpll.sat_solver().var_phase(Variable::new(0)),
        Some(false),
        "proof-tracking assumption solve should pre-apply the theory hint to SAT saved phases"
    );
}

#[test]
fn test_solve_reapplies_phase_hints_after_conflict_6296() {
    let phase_calls = Rc::new(Cell::new(0));
    let phase_atom = TermId::new(20);
    let blocker_atom = TermId::new(21);
    let theory = ReapplyingPhaseHintTheory::new(phase_atom, blocker_atom, Rc::clone(&phase_calls));
    let mut dpll = DpllT::new(3, theory);
    configure_phase_hint_test_solver(&mut dpll);
    dpll.register_theory_atom(phase_atom, 0);
    dpll.register_theory_atom(blocker_atom, 1);
    dpll.add_clause(vec![Literal::positive(Variable::new(2))]);

    let result = dpll.solve();
    assert!(
        matches!(result, Ok(SatResult::Sat(_))),
        "solve() should re-apply updated phase hints after a theory conflict, got {result:?}"
    );
    let model = match result {
        Ok(SatResult::Sat(model)) => model,
        _ => Vec::new(),
    };
    assert_eq!(
        model,
        vec![true, false, true],
        "solve() should honor the updated second-round theory hint",
    );
    assert!(
        phase_calls.get() > 2,
        "solve() should re-consult theory phase hints after the first conflict"
    );
}

#[test]
fn test_interruptible_step_reapplies_phase_hints_after_conflict_6296() {
    let phase_calls = Rc::new(Cell::new(0));
    let phase_atom = TermId::new(24);
    let blocker_atom = TermId::new(25);
    let theory = ReapplyingPhaseHintTheory::new(phase_atom, blocker_atom, Rc::clone(&phase_calls));
    let mut dpll = DpllT::new(3, theory);
    configure_phase_hint_test_solver(&mut dpll);
    dpll.register_theory_atom(phase_atom, 0);
    dpll.register_theory_atom(blocker_atom, 1);
    dpll.add_clause(vec![Literal::positive(Variable::new(2))]);

    let result = dpll.solve_step_interruptible(|| false);
    assert!(
        matches!(result, Ok(SolveStepResult::Done(SatResult::Sat(_)))),
        "interruptible step should re-apply updated phase hints after a theory conflict, got {result:?}"
    );
    let model = match result {
        Ok(SolveStepResult::Done(SatResult::Sat(model))) => model,
        _ => Vec::new(),
    };
    assert_eq!(
        model,
        vec![true, false, true],
        "interruptible step should honor the updated second-round theory hint",
    );
    assert!(
        phase_calls.get() > 2,
        "interruptible step should re-consult theory phase hints after the first conflict"
    );
}

#[test]
fn test_scope_selector_solve_uses_phase_hints_6296() {
    let phase_calls = Rc::new(Cell::new(0));
    let phase_atom = TermId::new(12);
    let theory = CountingPhaseHintTheory::new(phase_atom, Rc::clone(&phase_calls));
    let mut dpll = DpllT::new(2, theory);
    configure_phase_hint_test_solver(&mut dpll);
    dpll.register_theory_atom(phase_atom, 0);
    dpll.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);
    dpll.push();

    let result = dpll.solve();
    assert!(
        matches!(result, Ok(SatResult::Sat(_))),
        "expected SAT from scoped solve, got {result:?}"
    );
    let model = match result {
        Ok(SatResult::Sat(model)) => model,
        _ => Vec::new(),
    };
    assert_eq!(
        model,
        vec![false, true],
        "scope-selector solve should preserve the hinted false phase",
    );

    assert!(
        phase_calls.get() > 0,
        "scope-selector solve must consult suggest_phase for theory atoms"
    );
    assert_eq!(
        dpll.sat_solver().var_phase(Variable::new(0)),
        Some(false),
        "scope-selector solve should pre-apply the theory hint to SAT saved phases"
    );
}
