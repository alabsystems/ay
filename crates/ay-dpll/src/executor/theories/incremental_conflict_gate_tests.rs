// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fail-closed semantic conflict gate on the NON-SPLIT incremental pipeline
//! (`solve_incremental_theory_pipeline!`, both variants).
//!
//! Regression tests for the #8595 fail-open removal: a theory conflict whose
//! semantic verification fails must NEVER be learned as a global clause.
//! Before the fix, both the `Unsat` and `UnsatWithFarkas` arms learned such
//! conflicts anyway ("using conflict anyway (#8595)"), laundering theory
//! bugs into wrong UNSAT verdicts on satisfiable formulas. These tests drive
//! the pipeline with a mock theory that reports a *satisfiable* literal set
//! as a conflict and assert the solve degrades to `Unknown` instead of
//! reporting a false `unsat`.
//!
//! Completeness counterparts assert that genuinely UNSAT conflicts (which
//! pass `verify_conflict_semantic`) are still learned and drive the solve to
//! a real `unsat` — including Farkas conflicts WITHOUT a certificate, which
//! must stay learnable through the semantic backstop (the GCD-infeasibility
//! precedent from the lazy split loop fix).

use ay_core::{TermId, TheoryConflict, TheoryLit, TheoryPropagation, TheoryResult, TheorySolver};
use ay_frontend::parse;

use crate::executor_types::{Result, SolveResult};
use crate::Executor;

/// Mock theory that always reports a caller-chosen conflict from `check()`.
///
/// Used to exercise the pipeline's conflict-verification gates with (a) a
/// satisfiable literal set (semantic verification fails with `ConflictIsSat`
/// — the wrong-UNSAT laundering case) and (b) a genuinely UNSAT literal set
/// (verification succeeds — the completeness case).
struct MockConflictTheory {
    conflict: Vec<TheoryLit>,
    farkas_arm: bool,
}

impl MockConflictTheory {
    /// Inherent no-ops mirroring `LraSolver::set_terms`/`unset_terms`,
    /// required by the `persistent_theory: true` macro variant.
    fn set_terms(&mut self, _terms: &ay_core::TermStore) {}

    fn unset_terms(&mut self) {}
}

impl TheorySolver for MockConflictTheory {
    fn assert_literal(&mut self, _literal: TermId, _value: bool) {}

    fn check(&mut self) -> TheoryResult {
        if self.farkas_arm {
            // `TheoryConflict::new` carries NO Farkas certificate, so the
            // pipeline's certificate checks report a missing annotation and
            // the semantic backstop decides whether the conflict is learned.
            TheoryResult::UnsatWithFarkas(TheoryConflict::new(self.conflict.clone()))
        } else {
            TheoryResult::Unsat(self.conflict.clone())
        }
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        Vec::new()
    }

    fn push(&mut self) {}

    fn pop(&mut self) {}

    fn reset(&mut self) {}
}

impl Executor {
    /// Non-persistent variant of `solve_incremental_theory_pipeline!` driven
    /// by [`MockConflictTheory`] (mirrors `solve_propositional`).
    fn solve_with_mock_conflict_theory(
        &mut self,
        conflict: Vec<TheoryLit>,
        farkas_arm: bool,
    ) -> Result<SolveResult> {
        solve_incremental_theory_pipeline!(self,
            tag: "MockConflictGate",
            create_theory: MockConflictTheory { conflict: conflict.clone(), farkas_arm },
            extract_models: |_theory| TheoryModels::default(),
            track_theory_stats: false,
            set_unknown_on_error: false
        )
    }

    /// `persistent_theory: true` variant driven by [`MockConflictTheory`]
    /// (mirrors `solve_lra_incremental`).
    fn solve_with_mock_conflict_theory_persistent(
        &mut self,
        conflict: Vec<TheoryLit>,
        farkas_arm: bool,
    ) -> Result<SolveResult> {
        solve_incremental_theory_pipeline!(self,
            tag: "MockConflictGatePersistent",
            create_theory: MockConflictTheory { conflict: conflict.clone(), farkas_arm },
            extract_models: |_theory| TheoryModels::default(),
            track_theory_stats: false,
            set_unknown_on_error: false,
            persistent_theory: true
        )
    }
}

/// Executor with a single asserted Int atom `(> x 0)`.
///
/// The formula is SAT (x = 1), so a "conflict" consisting of the asserted
/// atom alone is a satisfiable literal set: semantic verification must
/// reject it, and learning its negation would force a wrong UNSAT.
fn setup_sat_single_atom() -> (Executor, Vec<TheoryLit>) {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (> x 0))
    "#;
    let commands = parse(input).expect("parse single-atom setup");
    let mut exec = Executor::new();
    for command in &commands {
        exec.execute(command).expect("execute setup command");
    }
    let atom = *exec
        .ctx
        .assertions
        .first()
        .expect("assertion root must exist");
    let conflict = vec![TheoryLit::new(atom, true)];
    (exec, conflict)
}

/// Executor with `(> x 2)` and `(< x 1)` asserted: genuinely UNSAT.
///
/// A conflict over both atoms IS semantically valid (LIA-infeasible), so the
/// gate must let it through and the learned clause must drive the solve to a
/// real propositional UNSAT.
fn setup_unsat_two_atoms() -> (Executor, Vec<TheoryLit>) {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (> x 2))
        (assert (< x 1))
    "#;
    let commands = parse(input).expect("parse two-atom setup");
    let mut exec = Executor::new();
    for command in &commands {
        exec.execute(command).expect("execute setup command");
    }
    assert_eq!(exec.ctx.assertions.len(), 2, "two assertion roots expected");
    let conflict = exec
        .ctx
        .assertions
        .iter()
        .map(|&atom| TheoryLit::new(atom, true))
        .collect();
    (exec, conflict)
}

/// Unsat arm, non-persistent variant: a semantically-SAT "conflict" must not
/// be learned. Before the #8595 fail-open removal this returned a wrong
/// `unsat` for the satisfiable formula `x > 0`.
#[test]
fn unsat_arm_rejects_satisfiable_conflict() {
    let (mut exec, conflict) = setup_sat_single_atom();
    let result = exec
        .solve_with_mock_conflict_theory(conflict, false)
        .expect("solve must not error");
    assert_eq!(
        result,
        SolveResult::Unknown,
        "unverifiable conflict must degrade to Unknown, not launder into wrong UNSAT"
    );
}

/// UnsatWithFarkas arm, non-persistent variant: a certificate-less,
/// semantically-SAT "conflict" must not be learned (backstop fail-close).
#[test]
fn farkas_arm_rejects_satisfiable_conflict() {
    let (mut exec, conflict) = setup_sat_single_atom();
    let result = exec
        .solve_with_mock_conflict_theory(conflict, true)
        .expect("solve must not error");
    assert_eq!(
        result,
        SolveResult::Unknown,
        "unverifiable Farkas conflict must degrade to Unknown, not launder into wrong UNSAT"
    );
}

/// Unsat arm, persistent-theory variant: same fail-close requirement.
#[test]
fn unsat_arm_rejects_satisfiable_conflict_persistent() {
    let (mut exec, conflict) = setup_sat_single_atom();
    let result = exec
        .solve_with_mock_conflict_theory_persistent(conflict, false)
        .expect("solve must not error");
    assert_eq!(
        result,
        SolveResult::Unknown,
        "unverifiable conflict must degrade to Unknown on the persistent-theory variant"
    );
}

/// UnsatWithFarkas arm, persistent-theory variant: same fail-close requirement.
#[test]
fn farkas_arm_rejects_satisfiable_conflict_persistent() {
    let (mut exec, conflict) = setup_sat_single_atom();
    let result = exec
        .solve_with_mock_conflict_theory_persistent(conflict, true)
        .expect("solve must not error");
    assert_eq!(
        result,
        SolveResult::Unknown,
        "unverifiable Farkas conflict must degrade to Unknown on the persistent-theory variant"
    );
}

/// Completeness: a semantically VALID conflict passes the gate, is learned,
/// and produces a genuine UNSAT (non-persistent variant).
#[test]
fn unsat_arm_learns_verified_conflict() {
    let (mut exec, conflict) = setup_unsat_two_atoms();
    let result = exec
        .solve_with_mock_conflict_theory(conflict, false)
        .expect("solve must not error");
    assert!(
        result.is_unsat(),
        "semantically verified conflict must still be learned and yield UNSAT, got {result:?}"
    );
}

/// Completeness: a VALID Farkas conflict WITHOUT a certificate stays
/// learnable through the semantic backstop (certificate downgrade must not
/// fail-close valid conflicts — GCD-infeasibility precedent).
#[test]
fn farkas_arm_learns_uncertified_valid_conflict() {
    let (mut exec, conflict) = setup_unsat_two_atoms();
    let result = exec
        .solve_with_mock_conflict_theory(conflict, true)
        .expect("solve must not error");
    assert!(
        result.is_unsat(),
        "valid certificate-less Farkas conflict must pass the semantic backstop and yield UNSAT, got {result:?}"
    );
}

/// Completeness on the persistent-theory variant.
#[test]
fn unsat_arm_learns_verified_conflict_persistent() {
    let (mut exec, conflict) = setup_unsat_two_atoms();
    let result = exec
        .solve_with_mock_conflict_theory_persistent(conflict, false)
        .expect("solve must not error");
    assert!(
        result.is_unsat(),
        "semantically verified conflict must still yield UNSAT on the persistent-theory variant, got {result:?}"
    );
}

/// Completeness on the persistent-theory variant, Farkas arm.
#[test]
fn farkas_arm_learns_uncertified_valid_conflict_persistent() {
    let (mut exec, conflict) = setup_unsat_two_atoms();
    let result = exec
        .solve_with_mock_conflict_theory_persistent(conflict, true)
        .expect("solve must not error");
    assert!(
        result.is_unsat(),
        "valid certificate-less Farkas conflict must yield UNSAT on the persistent-theory variant, got {result:?}"
    );
}
