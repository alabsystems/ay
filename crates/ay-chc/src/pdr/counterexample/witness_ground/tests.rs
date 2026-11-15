// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! STEP D reads a counterexample's derivation witness; PDR lists its steps
//! init -> bad; the exporter never writes a trace obligation it refutes.
//!
//! Measured on cb6192902: `ay --strict-proofs` on [`UNSAFE_HORN`] published
//! `unsat` whenever the front BMC probe found the counterexample within its
//! 1.5 s soft budget (BMC attaches a ground derivation), and `unknown` with
//! "UNSAFE counterexample does NOT ground-check (trace contradicts the
//! transition relation)" whenever it did not and PDR found it: 16 of 16 runs
//! with 16 copies pinned to one core, 0 of 20 runs alone. With `--stats`, the
//! PDR run's `002-trace-validity.smt2` (`expected-result: sat`) pinned both
//! `(= v0 0)` and `(= v0 5)`, and z3 answered `unsat`.

use super::super::{Counterexample, CounterexampleStep, DerivationWitness, DerivationWitnessEntry};
use crate::pdr::{PdrConfig, PdrResult, PdrSolver};
use crate::smt::SmtValue;
use crate::{ChcParser, ChcProblem};

/// The UNSAFE script of `strict_chc_spellings` (group_soundness): `inv(0)`,
/// closed under `+ 1`, `x > 5` is reached.
const UNSAFE_HORN: &str = "(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (inv x) (inv (+ x 1)))))
(assert (forall ((x Int)) (=> (and (inv x) (> x 5)) false)))
(check-sat)
";

/// The same clause shapes, but `inv` stops at 5: SAFE.
const SAFE_HORN: &str = "(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 5)) (inv (+ x 1)))))
(assert (forall ((x Int)) (=> (and (inv x) (> x 5)) false)))
(check-sat)
";

fn parse(script: &str) -> ChcProblem {
    ChcParser::parse(script).expect("parse HORN fixture")
}

/// PDR's counterexample for `problem` (deterministic: no wall-clock budget).
fn pdr_counterexample(problem: &ChcProblem) -> Counterexample {
    match PdrSolver::new(problem.clone(), PdrConfig::default()).solve() {
        PdrResult::Unsafe(cex) => cex,
        other => panic!("PDR must find the depth-6 counterexample, got {other:?}"),
    }
}

/// `(fact, transition, query)` clause indices of a three-clause fixture.
fn clause_roles(problem: &ChcProblem) -> (usize, usize, usize) {
    let clauses = problem.clauses();
    let find = |role: &dyn Fn(&crate::HornClause) -> bool| {
        clauses.iter().position(role).expect("fixture clause role")
    };
    (
        find(&|c| c.body.predicates.is_empty()),
        find(&|c| !c.body.predicates.is_empty() && !c.is_query()),
        find(&|c| c.is_query()),
    )
}

fn int_env(x: i128) -> ay_core::kani_compat::DetHashMap<String, SmtValue> {
    [("x".to_string(), SmtValue::Int(x))].into_iter().collect()
}

/// A counterexample laid out as PDR's `build_cex` lays out the one it finds
/// for [`UNSAFE_HORN`]. The witness is ROOT FIRST: each entry carries its
/// incoming clause, its chain child as premise, and that clause's query model
/// in the clause's own names (`x = 5` on the root: `inv(5) -> inv(6)`); the
/// level-0 leaf carries the fact clause and the fact model. The steps carry
/// the same models leaf first (init -> bad). `leaf_x` is the fact model's
/// value (0 for the genuine counterexample).
fn pdr_layout_cex(problem: &ChcProblem, root_x: i128, leaf_x: i128) -> Counterexample {
    let (fact, transition, query) = clause_roles(problem);
    let predicate = problem.predicates()[0].id;
    let entry =
        |level: usize, incoming: usize, x: i128, premises: Vec<usize>| DerivationWitnessEntry {
            predicate,
            level,
            state: crate::ChcExpr::Bool(true),
            incoming_clause: Some(incoming),
            premises,
            instances: int_env(x),
        };
    let mut entries: Vec<DerivationWitnessEntry> = (0..6)
        .map(|i| entry(6 - i, transition, 5 - i as i128, vec![i + 1]))
        .collect();
    entries[0].instances = int_env(root_x);
    entries.push(entry(0, fact, leaf_x, Vec::new()));
    let steps = entries
        .iter()
        .rev()
        .map(|e| {
            let x = match e.instances.get("x") {
                Some(SmtValue::Int(x)) => i64::try_from(*x).expect("small fixture value"),
                other => panic!("fixture instance {other:?}"),
            };
            CounterexampleStep::new(predicate, [("x".to_string(), x)].into_iter().collect())
        })
        .collect();
    Counterexample {
        steps,
        witness: Some(DerivationWitness {
            query_clause: Some(query),
            root: 0,
            entries,
        }),
        compact_derivation: None,
        ground_derivation: None,
    }
}

/// The root cause, on the engine itself: PDR's genuine counterexample is
/// confirmed through its witness alone (no carried derivation, no trace; the
/// trace form reports an empty trace as `Err`, the pre-fix STEP D outcome).
#[test]
fn step_d_confirms_the_pdr_counterexample_through_its_witness() {
    let problem = parse(UNSAFE_HORN);
    let cex = pdr_counterexample(&problem);
    assert!(
        cex.witness_ground_derivation_validates(&problem),
        "the PDR witness must re-shape into a validating ground derivation"
    );
    let witness_only = Counterexample {
        steps: Vec::new(),
        witness: cex.witness.clone(),
        compact_derivation: None,
        ground_derivation: None,
    };
    assert!(
        matches!(witness_only.ground_checks_unsafe(&problem), Ok(true)),
        "STEP D must confirm PDR's genuine counterexample from its witness"
    );
    assert!(matches!(cex.ground_checks_unsafe(&problem), Ok(true)));
}

/// PDR's steps run init -> bad, so the trace form does not refute them and the
/// trace-validity obligation exports (root first, time 0 was pinned to the
/// root's `x = 5` against `init`'s `x = 0`: `Ok(false)`, and an
/// `expected-result: sat` obligation that z3 answered `unsat`).
#[test]
fn pdr_steps_run_init_to_bad_and_export_an_unrefuted_obligation() {
    let problem = parse(UNSAFE_HORN);
    let cex = pdr_counterexample(&problem);
    assert!(
        !matches!(cex.trace_validity_ground_evaluates(&problem), Ok(false)),
        "PDR's trace must not contradict init (steps listed bad -> init)"
    );
    let obligations = cex
        .trace_validity_replay_obligations(&problem)
        .expect("PDR's trace-validity obligation must export");
    assert_eq!(obligations.len(), 1);
}

/// The same, on a fixed witness (independent of how PDR's search runs): the
/// trace form cannot pin the successor states (`Err`), the witness form
/// confirms, and the obligation exports.
#[test]
fn step_d_confirms_a_pdr_layout() {
    let problem = parse(UNSAFE_HORN);
    let cex = pdr_layout_cex(&problem, 5, 0);
    assert!(cex.trace_validity_ground_evaluates(&problem).is_err());
    assert!(matches!(cex.ground_checks_unsafe(&problem), Ok(true)));
    assert!(cex.trace_validity_replay_obligations(&problem).is_ok());
}

/// The pre-fix PDR layout (steps root first): STEP D still confirms the
/// counterexample through its witness, but the trace form refutes the steps
/// and the exporter refuses to write them as an `expected-result: sat`
/// obligation (before the guard it exported `(= v0 0)` with `(= v0 5)`).
#[test]
fn the_exporter_refuses_a_trace_its_own_evaluation_refutes() {
    let problem = parse(UNSAFE_HORN);
    let mut cex = pdr_layout_cex(&problem, 5, 0);
    cex.steps.reverse();
    assert!(matches!(
        cex.trace_validity_ground_evaluates(&problem),
        Ok(false)
    ));
    assert!(matches!(cex.ground_checks_unsafe(&problem), Ok(true)));
    let error = cex
        .trace_validity_replay_obligations(&problem)
        .expect_err("a refuted trace-validity obligation must not be exported");
    assert!(error.to_string().contains("to false"), "{error}");
}

/// Negative twin: a witness whose root instance contradicts its premise (the
/// root claims `inv(4) -> inv(5)`, its premise derives `inv(5)`, and `inv(5)`
/// does not violate `x > 5`) builds a candidate that the validator rejects.
#[test]
fn step_d_rejects_a_witness_with_a_corrupted_instance() {
    let problem = parse(UNSAFE_HORN);
    let cex = pdr_layout_cex(&problem, 4, 0);
    assert!(cex.witness_ground_derivation(&problem).is_some());
    assert!(!cex.witness_ground_derivation_validates(&problem));
    assert!(!matches!(cex.ground_checks_unsafe(&problem), Ok(true)));
}

/// Negative twin: a witness whose leaf is not an initial state (`x = 1`
/// against the fact `x = 0`) builds a candidate that the validator rejects.
#[test]
fn step_d_rejects_a_witness_that_does_not_start_in_init() {
    let problem = parse(UNSAFE_HORN);
    let cex = pdr_layout_cex(&problem, 5, 1);
    assert!(cex.witness_ground_derivation(&problem).is_some());
    assert!(!cex.witness_ground_derivation_validates(&problem));
    assert!(!matches!(cex.ground_checks_unsafe(&problem), Ok(true)));
}

/// Negative twin: the genuine UNSAFE witness, checked against the SAFE twin
/// (same clause shapes, the transition guarded by `x < 5`), builds a candidate
/// that the validator rejects: the root step fires the transition at `x = 5`.
#[test]
fn step_d_rejects_the_unsafe_witness_on_the_safe_problem() {
    let safe = parse(SAFE_HORN);
    let cex = pdr_layout_cex(&parse(UNSAFE_HORN), 5, 0);
    assert!(cex.witness_ground_derivation(&safe).is_some());
    assert!(!cex.witness_ground_derivation_validates(&safe));
    assert!(!matches!(cex.ground_checks_unsafe(&safe), Ok(true)));
}

/// A witness that names a non-query clause as the violated query (a
/// transform-space index) is re-resolved by content: the derivation ends in
/// the problem's own query clause, and validates only because it is one.
#[test]
fn step_d_reresolves_a_witness_whose_query_is_not_a_query() {
    let problem = parse(UNSAFE_HORN);
    let (_, transition, query) = clause_roles(&problem);
    let mut cex = pdr_layout_cex(&problem, 5, 0);
    if let Some(witness) = cex.witness.as_mut() {
        witness.query_clause = Some(transition);
    }
    let derivation = cex
        .witness_ground_derivation(&problem)
        .expect("the root's query is re-resolved by content");
    assert_eq!(derivation.steps[derivation.query_step].clause_index, query);
    assert!(matches!(cex.ground_checks_unsafe(&problem), Ok(true)));
    let safe = parse(SAFE_HORN);
    assert!(!matches!(cex.ground_checks_unsafe(&safe), Ok(true)));
}

/// Negative twin: a cyclic witness (an otherwise well-shaped transition entry
/// whose premise is the root) names no derivation, and the walk terminates.
#[test]
fn step_d_rejects_a_cyclic_witness() {
    let problem = parse(UNSAFE_HORN);
    let mut cex = pdr_layout_cex(&problem, 5, 0);
    if let Some(witness) = cex.witness.as_mut() {
        witness.entries[5].premises = vec![0];
    }
    assert!(cex.witness_ground_derivation(&problem).is_none());
    assert!(!matches!(cex.ground_checks_unsafe(&problem), Ok(true)));
}
