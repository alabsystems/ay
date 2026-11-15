// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used, clippy::panic)]

use crate::engine_result::VerifiedChcResult;
use crate::pdr::config::PdrConfig;
use crate::pdr::solver::PdrSolver;
use crate::{ChcExpr, ChcParser};

/// The model-checker-consumer termination VC of
/// `while i < max_len invariant i <= max_len decreases max_len - i { i += 1 }`
/// over `usize`, as the native lane encodes it (captured with
/// `MODEL_CHECKER_CONSUMER_DUMP_CHC` from `tests/ui/trust/contract_projection_named_params_verify.rs`):
/// one nullary `error` predicate whose single fact is the whole ranking
/// condition, so every variable is fact-local.
const TERMINATION_VC: &str = r#"(set-logic HORN)
(declare-var max_len (_ BitVec 64))
(declare-var i (_ BitVec 64))
(declare-var guard_overflow Bool)
(declare-rel error ())
(rule (=> (and (bvule (bvsub max_len i) (bvsub max_len (bvadd #x0000000000000001 i))) (bvult i max_len) (not guard_overflow)) error))
(query error)"#;

/// The same VC with the loop invariant `i <= max_len` folded into the fact,
/// the second encoding the compiler emits for this row.
const TERMINATION_VC_WITH_INVARIANT: &str = r#"(set-logic HORN)
(declare-var max_len (_ BitVec 64))
(declare-var i (_ BitVec 64))
(declare-var guard_overflow Bool)
(declare-rel error ())
(rule (=> (and (bvule (bvsub max_len i) (bvsub max_len (bvadd #x0000000000000001 i))) (bvule i max_len) (bvult i max_len) (not guard_overflow)) error))
(query error)"#;

/// Run the acyclic safety check under the proof-run configuration.
///
/// `solve_pdr_proof` keeps the caller's clauses (`preserve_original_clauses`),
/// so a nullary `error` predicate survives as a predicate with a fact and a
/// query. The ordinary solve-time expansion would inline it into a
/// pure-constraint query instead and never reach the model closure.
fn acyclic_model(smt2: &str) -> Option<crate::pdr::model::InvariantModel> {
    let config = PdrConfig {
        preserve_original_clauses: true,
        ..PdrConfig::default()
    };
    let mut solver = PdrSolver::new(ChcParser::parse(smt2).unwrap(), config);
    solver.try_acyclic_safety_proof()
}

fn only_interpretation(
    model: &crate::pdr::model::InvariantModel,
    smt2: &str,
    name: &str,
) -> ChcExpr {
    let problem = ChcParser::parse(smt2).unwrap();
    let pred = problem.lookup_predicate(name).unwrap();
    model.get(&pred).unwrap().formula.clone()
}

#[test]
fn nullary_fact_with_only_local_variables_is_decided_by_acyclic_safety() {
    // Before the closure, the queries were proven unreachable here and the
    // model `error := <the fact, with its locals free>` was then refused by
    // verify_model's free-variable guard, so this returned None and the solve
    // fell through to the budget-sensitive full PDR search.
    for smt2 in [TERMINATION_VC, TERMINATION_VC_WITH_INVARIANT] {
        let model = acyclic_model(smt2).expect("acyclic safety decides the termination VC");
        assert_eq!(
            only_interpretation(&model, smt2, "error"),
            ChcExpr::Bool(false),
            "the fact is unsatisfiable on its own, so `error` is interpreted as false"
        );
    }
}

#[test]
fn termination_vc_is_a_proof_grade_safe() {
    for smt2 in [TERMINATION_VC, TERMINATION_VC_WITH_INVARIANT] {
        let mut config = PdrConfig::production(false).with_strict_proofs(true);
        config.solve_timeout = Some(std::time::Duration::from_secs(30));
        let run = crate::engines::solve_pdr_proof_from_str(smt2, config).unwrap();
        assert!(
            matches!(run.result(), VerifiedChcResult::Safe(_)),
            "the u64 ranking VC is safe and must be admitted: {:?}",
            run.result()
        );
    }
}

#[test]
fn nullary_predicate_with_a_satisfiable_local_fact_closes_to_true() {
    // `p` is reachable (x > 0 has models), but no query can fire: the query's
    // own constraint is contradictory. `exists x. x > 0` is the closed `true`.
    let smt2 = r#"(set-logic HORN)
(declare-var x Int)
(declare-var y Int)
(declare-rel p ())
(rule (=> (> x 0) p))
(rule (=> (and p (> y 5) (< y 3)) false))"#;
    let model = acyclic_model(smt2).expect("the closed model verifies");
    assert_eq!(only_interpretation(&model, smt2, "p"), ChcExpr::Bool(true));
}

#[test]
fn predicate_with_arguments_and_a_satisfiable_local_fact_still_bails() {
    // `exists y. x = y + 1 /\ y > 0` over the head argument `x` needs quantifier
    // elimination; the builder must not emit a model with `y` free.
    let smt2 = r#"(set-logic HORN)
(declare-var x Int)
(declare-var y Int)
(declare-rel p (Int))
(rule (=> (and (= x (+ y 1)) (> y 0)) (p x)))
(rule (=> (and (p x) (< x 0)) false))"#;
    assert!(acyclic_model(smt2).is_none());
}

#[test]
fn reachable_nullary_error_is_never_closed_into_a_proof() {
    // Negative control: the same shape with a satisfiable fact and a live
    // query is UNSAFE. The acyclic check must refuse it, and the proof run
    // must not report Safe.
    let smt2 = r#"(set-logic HORN)
(declare-var max_len (_ BitVec 64))
(declare-var i (_ BitVec 64))
(declare-rel error ())
(rule (=> (and (bvule (bvsub max_len i) (bvsub max_len (bvadd #x0000000000000001 i))) (bvule i max_len)) error))
(query error)"#;
    assert!(acyclic_model(smt2).is_none());
    let mut config = PdrConfig::production(false).with_strict_proofs(true);
    config.solve_timeout = Some(std::time::Duration::from_secs(30));
    let run = crate::engines::solve_pdr_proof_from_str(smt2, config).unwrap();
    assert!(
        !matches!(run.result(), VerifiedChcResult::Safe(_)),
        "i = max_len reaches error: {:?}",
        run.result()
    );
}
