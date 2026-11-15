// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Query-clause validation substitutes away every top-level definition, as
//! transition validation does, so a frame interpretation that pins a
//! clause-local validity array to a store chain does not keep the query
//! clause's body in the array theory (model-checker-consumer realloc-grow pre-discharge VC,
//! 2026-10-14).

#![allow(clippy::unwrap_used, clippy::panic)]

use super::*;
use crate::pdr::{InvariantModel, PdrConfig, PredicateInterpretation};
use crate::{ChcParser, ChcProblem, ClauseHead};

/// Six stack frames, thirteen of their fifteen pairs disjoint, and the
/// validity array pinned; the error fires when twelve of those pairs are not
/// all disjoint. The frame interpretation below is the fact's constraint, so
/// the query clause's body is `pin ∧ disjoint ∧ ¬disjoint'` with `disjoint'`
/// a subset of `disjoint`: unsatisfiable by propositional reasoning alone,
/// with the array pin irrelevant to the refutation (the shape of the
/// realloc VC's stack-frame validation queries).
const STACK_FRAMES: &str = r#"(set-logic HORN)
(declare-rel frame ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64)
  (_ BitVec 64) (Array (_ BitVec 32) Bool)))
(declare-var a (Array (_ BitVec 32) Bool))
(declare-var sb8 (_ BitVec 64))
(declare-var sb45 (_ BitVec 64))
(declare-var sb46 (_ BitVec 64))
(declare-var sb51 (_ BitVec 64))
(declare-var sb67 (_ BitVec 64))
(declare-var sb68 (_ BitVec 64))
(rule (=> (and (= a (store ((as const (Array (_ BitVec 32) Bool)) true) #x00000042 true))
               (not (= sb68 #x0000000000000000))
               (or (bvule (bvadd sb8 #x0000000000000010) sb45) (bvule (bvadd sb45 #x0000000000000010) sb8))
               (or (bvule (bvadd sb8 #x0000000000000010) sb46) (bvule (bvadd sb46 #x0000000000000010) sb8))
               (or (bvule (bvadd sb8 #x0000000000000010) sb51) (bvule (bvadd sb51 #x0000000000000020) sb8))
               (or (bvule (bvadd sb8 #x0000000000000010) sb67) (bvule (bvadd sb67 #x0000000000000010) sb8))
               (or (bvule (bvadd sb8 #x0000000000000010) sb68) (bvule (bvadd sb68 #x0000000000000018) sb8))
               (or (bvule (bvadd sb45 #x0000000000000010) sb46) (bvule (bvadd sb46 #x0000000000000010) sb45))
               (or (bvule (bvadd sb45 #x0000000000000010) sb51) (bvule (bvadd sb51 #x0000000000000020) sb45))
               (or (bvule (bvadd sb45 #x0000000000000010) sb67) (bvule (bvadd sb67 #x0000000000000010) sb45))
               (or (bvule (bvadd sb45 #x0000000000000010) sb68) (bvule (bvadd sb68 #x0000000000000018) sb45))
               (or (bvule (bvadd sb46 #x0000000000000010) sb51) (bvule (bvadd sb51 #x0000000000000020) sb46))
               (or (bvule (bvadd sb46 #x0000000000000010) sb67) (bvule (bvadd sb67 #x0000000000000010) sb46))
               (or (bvule (bvadd sb46 #x0000000000000010) sb68) (bvule (bvadd sb68 #x0000000000000018) sb46))
               (or (bvule (bvadd sb51 #x0000000000000020) sb67) (bvule (bvadd sb67 #x0000000000000010) sb51)))
          (frame sb8 sb45 sb46 sb51 sb67 sb68 a)))
(rule (=> (and (frame sb8 sb45 sb46 sb51 sb67 sb68 a)
               (not (and (not (= sb68 #x0000000000000000)) (or (bvule (bvadd sb8 #x0000000000000010) sb45) (bvule (bvadd sb45 #x0000000000000010) sb8)) (or (bvule (bvadd sb8 #x0000000000000010) sb51) (bvule (bvadd sb51 #x0000000000000020) sb8)) (or (bvule (bvadd sb8 #x0000000000000010) sb67) (bvule (bvadd sb67 #x0000000000000010) sb8)) (or (bvule (bvadd sb8 #x0000000000000010) sb68) (bvule (bvadd sb68 #x0000000000000018) sb8)) (or (bvule (bvadd sb45 #x0000000000000010) sb46) (bvule (bvadd sb46 #x0000000000000010) sb45)) (or (bvule (bvadd sb45 #x0000000000000010) sb51) (bvule (bvadd sb51 #x0000000000000020) sb45)) (or (bvule (bvadd sb45 #x0000000000000010) sb67) (bvule (bvadd sb67 #x0000000000000010) sb45)) (or (bvule (bvadd sb45 #x0000000000000010) sb68) (bvule (bvadd sb68 #x0000000000000018) sb45)) (or (bvule (bvadd sb46 #x0000000000000010) sb51) (bvule (bvadd sb51 #x0000000000000020) sb46)) (or (bvule (bvadd sb46 #x0000000000000010) sb67) (bvule (bvadd sb67 #x0000000000000010) sb46)) (or (bvule (bvadd sb46 #x0000000000000010) sb68) (bvule (bvadd sb68 #x0000000000000018) sb46)) (or (bvule (bvadd sb51 #x0000000000000020) sb67) (bvule (bvadd sb67 #x0000000000000010) sb51)))))
          false))"#;

/// The frame interpretation: the fact's constraint over its head variables,
/// without the conjuncts `drop` selects.
fn frame_model(problem: &ChcProblem, drop: impl Fn(&ChcExpr) -> bool) -> InvariantModel {
    let frame = problem.lookup_predicate("frame").unwrap();
    let fact = problem
        .clauses()
        .iter()
        .find(|clause| clause.body.predicates.is_empty())
        .unwrap();
    let ClauseHead::Predicate(_, args) = &fact.head else {
        panic!("the fact concludes the frame predicate");
    };
    let vars = args
        .iter()
        .map(|arg| match arg {
            ChcExpr::Var(var) => var.clone(),
            other => panic!("head argument {other} is not a variable"),
        })
        .collect();
    let constraint = fact.body.constraint.clone().unwrap();
    let kept = constraint
        .collect_conjuncts()
        .into_iter()
        .filter(|conjunct| !drop(conjunct));
    let mut model = InvariantModel::new();
    model.set(
        frame,
        PredicateInterpretation::new(vars, ChcExpr::and_all(kept)),
    );
    model
}

/// Per-rule validation on the ORIGINAL clauses, as the adaptive boundary runs
/// it for a back-translated model (no array scalarization).
fn validates(model: &InvariantModel, problem: &ChcProblem) -> bool {
    let config = PdrConfig {
        disable_array_scalarization: true,
        preserve_original_clauses: true,
        ..PdrConfig::default()
    };
    let mut verifier = PdrSolver::new(problem.clone(), config);
    verifier.verify_model_per_rule(model, std::time::Duration::from_secs(10))
}

/// Positive guard: with `a` substituted away the query clause's body is a
/// pure bit-vector refutation, and the valid model validates. (The raw body
/// also validates in this small case; the time it costs the executor is what
/// failed the realloc VC under load, and `group_adaptive`'s straight-line
/// test covers that end to end.)
#[test]
fn a_query_clause_over_a_pinned_array_validates() {
    let problem = ChcParser::parse(STACK_FRAMES).unwrap();
    assert!(validates(&frame_model(&problem, |_| false), &problem));
}

/// Negative twin: a frame interpretation without the `sb8`/`sb45`
/// disjointness lets the error fire, and the model must be refused.
#[test]
fn a_query_clause_violated_beside_a_pinned_array_is_refused() {
    let problem = ChcParser::parse(STACK_FRAMES).unwrap();
    let sb8_sb45 = |conjunct: &ChcExpr| {
        let vars = conjunct.vars();
        matches!(conjunct, ChcExpr::Op(ChcOp::Or, _))
            && vars.iter().any(|v| v.name == "sb8")
            && vars.iter().any(|v| v.name == "sb45")
    };
    assert!(!validates(&frame_model(&problem, sb8_sb45), &problem));
}
