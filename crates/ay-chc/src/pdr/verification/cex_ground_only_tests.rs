// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `Valid` rests only on a ground derivation validated on the verifier's
//! clauses; witness states and summaries never accept.
//!
//! The CHC differential gate found a PDR must summary that dropped a
//! `(mod y 3)` fact argument (claiming every `B(true, _)` reachable). The
//! counterexample it produced, `B(true, 7)` from that fact, passed the
//! witness-entry and root-state satisfiability checks on a SAFE system.

use super::*;
use crate::pdr::counterexample::{DerivationWitness, DerivationWitnessEntry};
use crate::pdr::{CounterexampleStep, PdrConfig};
use crate::smt::SmtValue;
use crate::{ChcExpr, ChcParser, ChcProblem, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ntest::timeout;

/// Safe (z3: `sat`): `B(true, m)` holds only for `m ∈ {0, 4}`, `B(false, m)`
/// for `m ∈ {4, 6}`.
const MOD_FACT_SAFE: &str = "(set-logic HORN)
(declare-fun U (Int) Bool)
(declare-fun B (Bool Int) Bool)
(assert (forall ((i Bool)) (B i 4)))
(assert (forall ((y Int)) (=> (and (>= y 0) (<= y 0)) (B true (mod y 3)))))
(assert (forall ((y Bool) (z Int)) (=> (and (B y z) (not y)) (B y 6))))
(assert (forall ((k Bool) (m Int)) (=> (and (B k m) (> m 6)) false)))
(check-sat)
";

fn verifier(problem: &ChcProblem) -> PdrSolver {
    let config = PdrConfig {
        preserve_original_clauses: true,
        disable_array_scalarization: true,
        disable_cex_replay: true,
        ..PdrConfig::default()
    };
    PdrSolver::new(problem.clone(), config)
}

/// The summary's counterexample: `B(true, 7)` "derived" by the `mod` fact
/// (clause 1) under `y = 0`, violating the query (clause 3).
fn summary_counterexample(problem: &ChcProblem) -> Counterexample {
    let b = problem.predicates()[1].id;
    let state = ChcExpr::and(
        ChcExpr::eq(
            ChcExpr::var(ChcVar::new("__p1_a0", ChcSort::Bool)),
            ChcExpr::Bool(true),
        ),
        ChcExpr::eq(
            ChcExpr::var(ChcVar::new("__p1_a1", ChcSort::Int)),
            ChcExpr::int(7),
        ),
    );
    let mut instances = FxHashMap::default();
    instances.insert("y".to_string(), SmtValue::Int(0));
    instances.insert("__p1_a0".to_string(), SmtValue::Bool(true));
    instances.insert("__p1_a1".to_string(), SmtValue::Int(7));
    let entry = DerivationWitnessEntry {
        predicate: b,
        level: 0,
        state,
        incoming_clause: Some(1),
        premises: Vec::new(),
        instances,
    };
    let mut assignments = FxHashMap::default();
    assignments.insert("__p1_a0".to_string(), 1);
    assignments.insert("__p1_a1".to_string(), 7);
    Counterexample::with_witness(
        vec![CounterexampleStep::new(b, assignments)],
        DerivationWitness {
            query_clause: Some(3),
            root: 0,
            entries: vec![entry],
        },
    )
}

#[test]
#[timeout(60_000)]
fn a_summary_counterexample_without_ground_evidence_is_never_valid() {
    let problem = ChcParser::parse(MOD_FACT_SAFE).expect("fixture parses");
    let cex = summary_counterexample(&problem);
    assert_ne!(
        verifier(&problem).verify_counterexample(&cex),
        CexVerificationResult::Valid,
        "the mod fact derives B(true, 0), not B(true, 7)"
    );
    assert!(verifier(&problem).confirm_counterexample(cex).is_err());
}
