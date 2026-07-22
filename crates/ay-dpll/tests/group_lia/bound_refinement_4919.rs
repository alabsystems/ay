// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for LRA bound-refinement plumbing (#4919).

use ay_core::{
    BoundRefinementRequest, Sort, TermId, TermStore, TheoryLit, TheoryPropagation, TheoryResult,
    TheorySolver, Tseitin,
};
use ay_dpll::{DpllT, SolveStepResult};
use ay_sat::SatResult;
use ntest::timeout;
use num_bigint::BigInt;
use num_rational::BigRational;
use std::collections::HashMap;

struct DummyBoundRefinementTheory {
    trigger_atom: TermId,
    bound_atom: TermId,
    asserted: HashMap<TermId, bool>,
    registered_atoms: Vec<TermId>,
    pending_bound_refinements: Vec<BoundRefinementRequest>,
}

impl DummyBoundRefinementTheory {
    fn new(trigger_atom: TermId, variable: TermId, bound_atom: TermId) -> Self {
        Self {
            trigger_atom,
            bound_atom,
            asserted: HashMap::default(),
            registered_atoms: Vec::new(),
            pending_bound_refinements: vec![BoundRefinementRequest {
                variable,
                rhs_term: None,
                bound_value: BigRational::from(BigInt::from(3)),
                is_upper: true,
                is_integer: false,
                reason: vec![TheoryLit::new(trigger_atom, true)],
            }],
        }
    }

    fn new_relative(trigger_atom: TermId, lhs: TermId, rhs: TermId, bound_atom: TermId) -> Self {
        Self {
            trigger_atom,
            bound_atom,
            asserted: HashMap::default(),
            registered_atoms: Vec::new(),
            pending_bound_refinements: vec![BoundRefinementRequest {
                variable: lhs,
                rhs_term: Some(rhs),
                bound_value: BigRational::from(BigInt::from(0)),
                is_upper: true,
                is_integer: false,
                reason: vec![TheoryLit::new(trigger_atom, true)],
            }],
        }
    }
}

impl TheorySolver for DummyBoundRefinementTheory {
    fn register_atom(&mut self, atom: TermId) {
        self.registered_atoms.push(atom);
    }

    fn assert_literal(&mut self, literal: TermId, value: bool) {
        self.asserted.insert(literal, value);
    }

    fn check(&mut self) -> TheoryResult {
        let bound_atom_registered = self.registered_atoms.contains(&self.bound_atom);
        if bound_atom_registered
            && self
                .asserted
                .get(&self.bound_atom)
                .copied()
                .unwrap_or(false)
        {
            // Produce a 2-literal conflict that is semantically valid:
            // trigger_atom=true AND bound_atom=true is contradictory
            // (the test setup uses trigger: x >= 5, bound: x <= 3).
            return TheoryResult::Unsat(vec![
                TheoryLit::new(self.trigger_atom, true),
                TheoryLit::new(self.bound_atom, true),
            ]);
        }
        debug_assert!(
            self.asserted
                .get(&self.trigger_atom)
                .copied()
                .unwrap_or(false),
            "trigger atom should be asserted by the SAT model"
        );
        TheoryResult::Sat
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        Vec::new()
    }

    fn push(&mut self) {}

    fn pop(&mut self) {}

    fn reset(&mut self) {
        self.asserted.clear();
    }

    fn take_bound_refinements(&mut self) -> Vec<BoundRefinementRequest> {
        std::mem::take(&mut self.pending_bound_refinements)
    }
}

struct InternalizeAwareTheory {
    trigger_atom: TermId,
    pending_bound_refinements: Vec<BoundRefinementRequest>,
    saw_internalize: bool,
}

impl InternalizeAwareTheory {
    fn new(trigger_atom: TermId, variable: TermId) -> Self {
        Self {
            trigger_atom,
            pending_bound_refinements: vec![BoundRefinementRequest {
                variable,
                rhs_term: None,
                bound_value: BigRational::from(BigInt::from(3)),
                is_upper: true,
                is_integer: false,
                reason: vec![TheoryLit::new(trigger_atom, true)],
            }],
            saw_internalize: false,
        }
    }
}

impl TheorySolver for InternalizeAwareTheory {
    fn register_atom(&mut self, atom: TermId) {
        if atom == self.trigger_atom {
            self.saw_internalize = true;
        }
    }

    fn assert_literal(&mut self, _literal: TermId, _value: bool) {}

    fn check(&mut self) -> TheoryResult {
        TheoryResult::Sat
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        Vec::new()
    }

    fn push(&mut self) {}

    fn pop(&mut self) {}

    fn reset(&mut self) {
        self.saw_internalize = false;
    }

    fn take_bound_refinements(&mut self) -> Vec<BoundRefinementRequest> {
        if self.saw_internalize {
            std::mem::take(&mut self.pending_bound_refinements)
        } else {
            Vec::new()
        }
    }
}

#[test]
#[timeout(60_000)]
fn test_dpll_step_plumbs_need_bound_refinements() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let trigger_atom = terms.mk_ge(x, five);
    let bound_atom = terms.mk_le(x, three);

    let tseitin = Tseitin::new(&terms).transform_all(&[trigger_atom]);
    let theory = DummyBoundRefinementTheory::new(trigger_atom, x, bound_atom);
    let mut dpll = DpllT::from_tseitin(&terms, &tseitin, theory);

    let requests = match dpll.solve_step().unwrap() {
        SolveStepResult::NeedBoundRefinements(requests) => requests,
        other => panic!("expected NeedBoundRefinements, got {other:?}"),
    };
    assert_eq!(requests.len(), 1);
    assert_eq!(requests[0].variable, x);
    assert_eq!(requests[0].rhs_term, None);
    assert!(requests[0].is_upper);
    assert_eq!(requests[0].reason, vec![TheoryLit::new(trigger_atom, true)]);

    assert!(
        dpll.apply_bound_refinement(bound_atom, &requests[0].reason),
        "bound refinement reasons should map to SAT literals"
    );

    match dpll.solve_step().unwrap() {
        SolveStepResult::Done(SatResult::Unsat(_)) => {}
        other => panic!("expected UNSAT after applying bound refinement, got {other:?}"),
    }
}

#[test]
#[timeout(60_000)]
fn test_bound_refinement_replay_registers_atom_with_fresh_theory() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let trigger_atom = terms.mk_ge(x, five);
    let bound_atom = terms.mk_le(x, three);

    let tseitin = Tseitin::new(&terms).transform_all(&[trigger_atom]);
    let theory = DummyBoundRefinementTheory::new(trigger_atom, x, bound_atom);
    let mut first_dpll = DpllT::from_tseitin(&terms, &tseitin, theory);

    let requests = match first_dpll.solve_step().unwrap() {
        SolveStepResult::NeedBoundRefinements(requests) => requests,
        other => panic!("expected NeedBoundRefinements, got {other:?}"),
    };
    drop(first_dpll);

    let theory = DummyBoundRefinementTheory::new(trigger_atom, x, bound_atom);
    let mut replay_dpll = DpllT::from_tseitin(&terms, &tseitin, theory);
    assert!(
        replay_dpll.apply_bound_refinement(bound_atom, &requests[0].reason),
        "bound refinement reasons should map to SAT literals"
    );

    match replay_dpll.solve_step().unwrap() {
        SolveStepResult::Done(SatResult::Unsat(_)) => {}
        SolveStepResult::NeedBoundRefinements(_) => {
            panic!("bound refinement replay should register the new atom with the fresh theory")
        }
        other => panic!("expected UNSAT after replaying bound refinement, got {other:?}"),
    }
}

#[test]
#[timeout(60_000)]
fn test_relative_bound_refinement_replay_registers_atom_with_fresh_theory() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let trigger_atom = terms.mk_ge(y, five);
    let bound_atom = terms.mk_le(y, three);

    let tseitin = Tseitin::new(&terms).transform_all(&[trigger_atom]);
    let theory = DummyBoundRefinementTheory::new_relative(trigger_atom, x, y, bound_atom);
    let mut first_dpll = DpllT::from_tseitin(&terms, &tseitin, theory);

    let requests = match first_dpll.solve_step().unwrap() {
        SolveStepResult::NeedBoundRefinements(requests) => requests,
        other => panic!("expected NeedBoundRefinements, got {other:?}"),
    };
    drop(first_dpll);

    let theory = DummyBoundRefinementTheory::new_relative(trigger_atom, x, y, bound_atom);
    let mut replay_dpll = DpllT::from_tseitin(&terms, &tseitin, theory);
    assert!(
        replay_dpll.apply_bound_refinement(bound_atom, &requests[0].reason),
        "relative bound refinement replay should map to SAT literals"
    );

    match replay_dpll.solve_step().unwrap() {
        SolveStepResult::Done(SatResult::Unsat(_)) => {}
        SolveStepResult::NeedBoundRefinements(_) => {
            panic!("relative bound refinement replay should register the new atom with the fresh theory")
        }
        other => panic!("expected UNSAT after replaying relative bound refinement, got {other:?}"),
    }
}

#[test]
#[timeout(60_000)]
fn test_lazy_solve_step_internalizes_theory_atoms_for_refinement_requests() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(BigRational::from(BigInt::from(0)));
    let trigger_atom = terms.mk_ge(x, zero);

    let tseitin = Tseitin::new(&terms).transform_all(&[trigger_atom]);
    let theory = InternalizeAwareTheory::new(trigger_atom, x);
    let mut dpll = DpllT::from_tseitin(&terms, &tseitin, theory);

    let requests = match dpll.solve_step().unwrap() {
        SolveStepResult::NeedBoundRefinements(requests) => requests,
        other => panic!("expected NeedBoundRefinements after lazy internalization, got {other:?}"),
    };
    assert!(
        requests
            .iter()
            .any(|req| req.variable == x && req.rhs_term.is_none() && req.is_upper),
        "expected refinement request for internalized trigger atom, got {requests:?}"
    );
}

#[test]
#[timeout(60_000)]
fn test_dpll_step_plumbs_relative_bound_refinements() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let trigger_atom = terms.mk_ge(y, five);
    let bound_atom = terms.mk_le(y, three);

    let tseitin = Tseitin::new(&terms).transform_all(&[trigger_atom]);
    let theory = DummyBoundRefinementTheory::new_relative(trigger_atom, x, y, bound_atom);
    let mut dpll = DpllT::from_tseitin(&terms, &tseitin, theory);

    let requests = match dpll.solve_step().unwrap() {
        SolveStepResult::NeedBoundRefinements(requests) => requests,
        other => panic!("expected NeedBoundRefinements, got {other:?}"),
    };
    assert_eq!(requests.len(), 1);
    assert_eq!(requests[0].variable, x);
    assert_eq!(requests[0].rhs_term, Some(y));
    assert_eq!(requests[0].bound_value, BigRational::from(BigInt::from(0)));
    assert!(requests[0].is_upper);
    assert_eq!(requests[0].reason, vec![TheoryLit::new(trigger_atom, true)]);

    assert!(
        dpll.apply_bound_refinement(bound_atom, &requests[0].reason),
        "relative bound refinement reasons should map to SAT literals"
    );

    match dpll.solve_step().unwrap() {
        SolveStepResult::Done(SatResult::Unsat(_)) => {}
        other => panic!("expected UNSAT after applying relative bound refinement, got {other:?}"),
    }
}
