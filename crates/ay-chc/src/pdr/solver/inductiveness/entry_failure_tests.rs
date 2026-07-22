// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::parser::ChcParser;
use crate::pdr::config::PdrConfig;
use crate::pdr::solver::{EntryInductiveFailureReason, PdrSolver};
use crate::ChcExpr;

fn entry_failure_count(solver: &PdrSolver, reason: EntryInductiveFailureReason) -> usize {
    solver
        .telemetry
        .entry_inductive_failure_counts
        .get(&reason)
        .copied()
        .unwrap_or(0)
}

#[test]
fn test_is_entry_inductive_records_sat_hyperedge_reason() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun p (Int) Bool)
(declare-fun r (Int) Bool)
(declare-fun q (Int) Bool)
(assert (forall ((x Int)) (=> (= x 1) (p x))))
(assert (forall ((x Int)) (=> (= x 1) (r x))))
(assert (forall ((x Int) (y Int) (z Int))
  (=> (and (p x) (r z) (= y x))
      (q y))))
(check-sat)
"#;

    let mut solver = PdrSolver::new(
        ChcParser::parse(smt2).expect("entry-hyperedge test SMT2 must parse"),
        PdrConfig::default(),
    );
    let q = solver
        .problem
        .lookup_predicate("q")
        .expect("predicate q must exist");
    let q_var = solver
        .canonical_vars(q)
        .expect("predicate q must have canonical vars")[0]
        .clone();
    let invariant = ChcExpr::le(ChcExpr::var(q_var), ChcExpr::Int(0));

    assert!(
        !solver.is_entry_inductive(&invariant, q, 2),
        "hyperedge SAT path should conservatively reject entry-inductiveness"
    );
    assert_eq!(
        entry_failure_count(&solver, EntryInductiveFailureReason::SatHyperedge),
        1,
        "expected sat_hyperedge failure counter increment"
    );
}

#[test]
fn test_is_entry_inductive_records_entry_cegar_disabled_reason() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun p (Int) Bool)
(declare-fun q (Int) Bool)
(assert (forall ((x Int) (y Int))
  (=> (and (p x) (= y (+ x 1)))
      (q y))))
(check-sat)
"#;

    let mut solver = PdrSolver::new(
        ChcParser::parse(smt2).expect("entry-cegar-disabled test SMT2 must parse"),
        PdrConfig {
            use_entry_cegar_discharge: false,
            ..PdrConfig::default()
        },
    );
    let q = solver
        .problem
        .lookup_predicate("q")
        .expect("predicate q must exist");
    let q_var = solver
        .canonical_vars(q)
        .expect("predicate q must have canonical vars")[0]
        .clone();
    let invariant = ChcExpr::le(ChcExpr::var(q_var), ChcExpr::Int(0));

    assert!(
        !solver.is_entry_inductive(&invariant, q, 2),
        "entry-cegar disabled path should conservatively reject entry-inductiveness"
    );
    assert_eq!(
        entry_failure_count(&solver, EntryInductiveFailureReason::EntryCegarDisabled),
        1,
        "expected entry_cegar_disabled failure counter increment"
    );
}

#[test]
fn test_is_entry_inductive_records_entry_cegar_budget_exhausted_reason() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun p (Int) Bool)
(declare-fun q (Int) Bool)
(assert (forall ((x Int) (y Int))
  (=> (and (p x) (= y (+ x 1)))
      (q y))))
(check-sat)
"#;

    let mut solver = PdrSolver::new(
        ChcParser::parse(smt2).expect("entry-cegar-budget test SMT2 must parse"),
        PdrConfig::default(),
    );
    let q = solver
        .problem
        .lookup_predicate("q")
        .expect("predicate q must exist");
    let q_var = solver
        .canonical_vars(q)
        .expect("predicate q must have canonical vars")[0]
        .clone();
    let invariant = ChcExpr::le(ChcExpr::var(q_var), ChcExpr::Int(0));
    solver.caches.entry_cegar_budget.insert(q, 0);

    assert!(
        !solver.is_entry_inductive(&invariant, q, 2),
        "budget-exhausted path should conservatively reject entry-inductiveness"
    );
    assert_eq!(
        entry_failure_count(
            &solver,
            EntryInductiveFailureReason::EntryCegarBudgetExhausted
        ),
        1,
        "expected entry_cegar_budget_exhausted failure counter increment"
    );
}
