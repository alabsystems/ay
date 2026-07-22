// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Tests for ground-table read concretization (parity item 4, Stage 1).
//! The mini/hazard fixtures are ported from an internal design-B prototype
//! battery.

use super::*;
use crate::adaptive::{AdaptiveConfig, AdaptivePortfolio};
use crate::parser::ChcParser;

fn adaptive_verdict(problem: ChcProblem) -> crate::VerifiedChcResult {
    AdaptivePortfolio::new(
        problem,
        AdaptiveConfig::test_default().with_time_budget(std::time::Duration::from_secs(20)),
    )
    .solve()
}

fn parse(smt: &str) -> ChcProblem {
    let problem =
        ChcParser::parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"));
    problem
        .validate()
        .unwrap_or_else(|err| panic!("CHC validation failed: {err}\nSMT2:\n{smt}"));
    problem
}

/// Safe 3-hop pin-table chain: the table A carries three pins along the DAG
/// and the query needs x = 9, which the scalar chain never reaches.
const MINI_SAFE: &str = r#"
(set-logic HORN)
(declare-var A (Array (_ BitVec 32) (_ BitVec 32)))
(declare-var x (_ BitVec 8))
(declare-var y (_ BitVec 8))
(declare-rel P0 ((Array (_ BitVec 32) (_ BitVec 32)) (_ BitVec 8)))
(declare-rel P1 ((Array (_ BitVec 32) (_ BitVec 32)) (_ BitVec 8)))
(declare-rel P2 ((Array (_ BitVec 32) (_ BitVec 32)) (_ BitVec 8)))
(declare-rel error ())
(rule (=> (and (= (select A #x00000001) #x00000005) (= (select A #x00000002) #x00000008) (= x #x01)) (P0 A x)))
(rule (=> (and (P0 A x) (= (select A #x00000003) #x00000002) (= y (bvadd x #x01))) (P1 A y)))
(rule (=> (and (P1 A x)) (P2 A x)))
(rule (=> (and (P2 A x) (= x #x09)) error))
(query error)
"#;

/// Unsafe twin of MINI_SAFE: query needs x = 2, which IS reached.
const MINI_UNSAFE: &str = r#"
(set-logic HORN)
(declare-var A (Array (_ BitVec 32) (_ BitVec 32)))
(declare-var x (_ BitVec 8))
(declare-var y (_ BitVec 8))
(declare-rel P0 ((Array (_ BitVec 32) (_ BitVec 32)) (_ BitVec 8)))
(declare-rel P1 ((Array (_ BitVec 32) (_ BitVec 32)) (_ BitVec 8)))
(declare-rel P2 ((Array (_ BitVec 32) (_ BitVec 32)) (_ BitVec 8)))
(declare-rel error ())
(rule (=> (and (= (select A #x00000001) #x00000005) (= (select A #x00000002) #x00000008) (= x #x01)) (P0 A x)))
(rule (=> (and (P0 A x) (= (select A #x00000003) #x00000002) (= y (bvadd x #x01))) (P1 A y)))
(rule (=> (and (P1 A x)) (P2 A x)))
(rule (=> (and (P2 A x) (= x #x02)) error))
(query error)
"#;

/// NEGATED pin hazard (load-bearing bail): the error rule reads the SAME
/// table cell under negation. Concretizing the positive pin while the
/// negative read remains (or replacing both) would flip Safe -> spurious
/// Unsafe, so the whole pass must go identity.
const HAZARD_NEGATED_PIN: &str = r#"
(set-logic HORN)
(declare-var A (Array (_ BitVec 32) (_ BitVec 32)))
(declare-var x (_ BitVec 8))
(declare-rel P0 ((Array (_ BitVec 32) (_ BitVec 32)) (_ BitVec 8)))
(declare-rel error ())
(rule (=> (and (= (select A #x00000001) #x00000005) (= x #x01)) (P0 A x)))
(rule (=> (and (P0 A x) (not (= (select A #x00000001) #x00000005))) error))
(query error)
"#;

/// Conflicting pins on one lane: rule 1 pins A[1]=5, rule 2 pins A[1]=6 on
/// the SAME threaded lane. No single table satisfies both -> bail.
const CONFLICTING_PINS: &str = r#"
(set-logic HORN)
(declare-var A (Array (_ BitVec 32) (_ BitVec 32)))
(declare-var x (_ BitVec 8))
(declare-rel P0 ((Array (_ BitVec 32) (_ BitVec 32)) (_ BitVec 8)))
(declare-rel error ())
(rule (=> (and (= (select A #x00000001) #x00000005) (= x #x01)) (P0 A x)))
(rule (=> (and (P0 A x) (= (select A #x00000001) #x00000006)) error))
(query error)
"#;

/// Equal-value pins across rules on one lane: must fire (not bail).
const MULTI_RULE_EQUAL_PINS: &str = r#"
(set-logic HORN)
(declare-var A (Array (_ BitVec 32) (_ BitVec 32)))
(declare-var x (_ BitVec 8))
(declare-rel P0 ((Array (_ BitVec 32) (_ BitVec 32)) (_ BitVec 8)))
(declare-rel error ())
(rule (=> (and (= (select A #x00000001) #x00000005) (= x #x01)) (P0 A x)))
(rule (=> (and (P0 A x) (= (select A #x00000001) #x00000005) (= x #x09)) error))
(query error)
"#;

/// Symbolic index + store (check_wrap_offset shape): must stay identity.
const SYMBOLIC_INDEX_STORE: &str = r#"
(set-logic HORN)
(declare-var A (Array (_ BitVec 32) (_ BitVec 32)))
(declare-var B (Array (_ BitVec 32) (_ BitVec 32)))
(declare-var i (_ BitVec 32))
(declare-rel P0 ((Array (_ BitVec 32) (_ BitVec 32)) (_ BitVec 32)))
(declare-rel error ())
(rule (=> (and (= (select A (bvadd i #x00000001)) #x00000005)) (P0 A i)))
(rule (=> (and (P0 A i) (= B (store A i #x00000002)) (= (select B #x00000000) #x00000007)) error))
(query error)
"#;

fn apply(problem: &ChcProblem) -> Option<ChcProblem> {
    GroundTableReadConcretizer::new().apply(problem)
}

#[test]
fn mini_safe_concretizes_and_pins_are_gone() {
    let problem = parse(MINI_SAFE);
    let rewritten = apply(&problem).expect("pin-table chain must concretize");
    for clause in rewritten.clauses() {
        if let Some(constraint) = clause.body.constraint.as_ref() {
            let printed = format!("{constraint:?}");
            assert!(
                !printed.contains("Select"),
                "no select may survive concretization: {printed}"
            );
        }
    }
    // Signatures untouched (DeadParamEliminator slices downstream).
    assert_eq!(
        rewritten.predicates().len(),
        problem.predicates().len(),
        "signatures must be untouched"
    );
}

#[test]
fn hazard_negated_pin_bails_to_identity() {
    let problem = parse(HAZARD_NEGATED_PIN);
    assert!(
        apply(&problem).is_none(),
        "negated pin must bail the WHOLE pass (load-bearing polarity check)"
    );
}

#[test]
fn conflicting_pins_bail_to_identity() {
    let problem = parse(CONFLICTING_PINS);
    assert!(
        apply(&problem).is_none(),
        "conflicting pin values on one lane must bail"
    );
}

#[test]
fn multi_rule_equal_value_pins_fire() {
    let problem = parse(MULTI_RULE_EQUAL_PINS);
    let rewritten = apply(&problem).expect("equal duplicate pins across rules must not bail");
    for clause in rewritten.clauses() {
        if let Some(constraint) = clause.body.constraint.as_ref() {
            let printed = format!("{constraint:?}");
            assert!(!printed.contains("Select"), "pins must be eliminated");
        }
    }
}

#[test]
fn symbolic_index_and_store_stay_identity() {
    let problem = parse(SYMBOLIC_INDEX_STORE);
    assert!(
        apply(&problem).is_none(),
        "symbolic select index + store (check_wrap_offset shape) must stay identity"
    );
}

#[test]
fn transform_reports_equisat_grade_obligations() {
    let problem = parse(MINI_SAFE);
    let result = Box::new(GroundTableReadConcretizer::new()).transform(problem);
    let memory = result.transform_memory();
    assert!(
        !memory.is_identity_grade(),
        "a real rewrite must not be identity-grade"
    );
    assert!(
        memory.is_equisat_grade(),
        "concretization is equisat-grade: {}",
        memory.diagnostic_summary()
    );
    assert!(memory.has_obligation("ground-table-read-concretization"));
    assert!(memory.has_obligation("original-validation-on-safe"));
    assert!(memory.has_obligation("original-replay-on-unsafe"));
}

#[test]
fn kill_switch_reports_identity() {
    // Exercised via the pass-internal env check without mutating process env
    // (parallel tests): the transform on an array-free problem is identity.
    let problem = parse(
        r#"
(set-logic HORN)
(declare-var x Int)
(declare-rel P (Int))
(declare-rel error ())
(rule (=> (= x 1) (P x)))
(rule (=> (and (P x) (= x 2)) error))
(query error)
"#,
    );
    let result = Box::new(GroundTableReadConcretizer::new()).transform(problem);
    assert!(
        result.transform_memory().is_identity_grade(),
        "array-free problems must be identity"
    );
}

// ---------------------------------------------------------------------------
// Differential verdict preservation (orig vs concretized), end to end
// ---------------------------------------------------------------------------

#[test]
fn mini_safe_verdict_preserved_end_to_end() {
    let original = parse(MINI_SAFE);
    let concretized = apply(&original).expect("must concretize");

    let orig_verdict = adaptive_verdict(original);
    let conc_verdict = adaptive_verdict(concretized);
    assert!(
        !matches!(orig_verdict, crate::VerifiedChcResult::Unsafe(_)),
        "MINI_SAFE original must not be unsafe"
    );
    assert!(
        !matches!(conc_verdict, crate::VerifiedChcResult::Unsafe(_)),
        "MINI_SAFE concretized must not be unsafe"
    );
}

#[test]
fn mini_unsafe_verdict_preserved_end_to_end() {
    let original = parse(MINI_UNSAFE);
    let concretized = apply(&original).expect("must concretize");

    let orig_verdict = adaptive_verdict(original);
    let conc_verdict = adaptive_verdict(concretized);
    assert!(
        !matches!(orig_verdict, crate::VerifiedChcResult::Safe(_)),
        "MINI_UNSAFE original must not be safe"
    );
    assert!(
        !matches!(conc_verdict, crate::VerifiedChcResult::Safe(_)),
        "MINI_UNSAFE concretized must not be safe"
    );
}

// ---------------------------------------------------------------------------
// Phase 1: clause-local array alias elimination
// ---------------------------------------------------------------------------

/// A clause-local alias of the table (ClauseInliner bridge shape) must be
/// projected so the pin analysis still fires.
#[test]
fn local_alias_projection_enables_concretization() {
    let problem = parse(
        r#"
(set-logic HORN)
(declare-var A (Array Int Int))
(declare-var B (Array Int Int))
(declare-var x Int)
(declare-rel P0 ((Array Int Int) Int))
(declare-rel error ())
(rule (=> (and (= B A) (= (select B 1) 5) (= x 1)) (P0 A x)))
(rule (=> (and (P0 A x) (= x 9)) error))
(query error)
"#,
    );
    let rewritten = apply(&problem).expect("alias + pin must concretize");
    for clause in rewritten.clauses() {
        if let Some(constraint) = clause.body.constraint.as_ref() {
            let printed = format!("{constraint:?}");
            assert!(
                !printed.contains("Select"),
                "pin must be replaced: {printed}"
            );
            assert!(
                !printed.contains("\"B\""),
                "local alias var must be projected away: {printed}"
            );
        }
    }
}

/// An equality chain bridging two SHARED arrays through a local is fully
/// unified: every class member (including argument variables) substitutes
/// to the representative, the head arguments unify, and no array equality
/// survives (solved-form elimination is exact for top-level body
/// equalities).
#[test]
fn shared_shared_bridge_unifies_through_args() {
    let problem = parse(
        r#"
(set-logic HORN)
(declare-var A (Array Int Int))
(declare-var B (Array Int Int))
(declare-var v (Array Int Int))
(declare-var x Int)
(declare-rel P0 ((Array Int Int) (Array Int Int) Int))
(declare-rel error ())
(rule (=> (and (= A v) (= v B) (= x 1)) (P0 A B x)))
(rule (=> (and (P0 A B x) (= x 9)) error))
(query error)
"#,
    );
    let rewritten = apply(&problem).expect("alias unification must fire");
    let clause0 = &rewritten.clauses()[0];
    let printed = format!("{:?}", clause0.body.constraint);
    assert!(
        !printed.contains("\"v\"") && !printed.contains("\"B\""),
        "bridge and non-representative vars must be unified away: {printed}"
    );
    let head = format!("{:?}", clause0.head);
    assert!(
        !head.contains("\"B\""),
        "head argument must be rewritten to the representative: {head}"
    );
}

/// Cyclic local aliases (duplicate equality in both orientations) must be
/// canonicalized to one representative, not silently dropped.
#[test]
fn cyclic_local_aliases_are_canonicalized() {
    let problem = parse(
        r#"
(set-logic HORN)
(declare-var u (Array Int Int))
(declare-var v (Array Int Int))
(declare-var x Int)
(declare-rel P0 (Int))
(declare-rel error ())
(rule (=> (and (= u v) (= v u) (= (select u 1) 5) (= (select v 1) 5) (= x 1)) (P0 x)))
(rule (=> (and (P0 x) (= x 9)) error))
(query error)
"#,
    );
    let rewritten = apply(&problem).expect("cyclic aliases + pins must concretize");
    let printed = format!("{:?}", rewritten.clauses()[0].body.constraint);
    assert!(
        !printed.contains("Select"),
        "pins on the canonical var must be replaced: {printed}"
    );
}
