// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};

const UNSAFE: &str = r#"
    (set-logic HORN)
    (declare-fun P ((Array (_ BitVec 4) Bool) Bool) Bool)
    (assert (P ((as const (Array (_ BitVec 4) Bool)) false) true))
    (assert (forall ((|ay!nullary!0| (Array (_ BitVec 4) Bool)) (b Bool))
      (=> (and (P |ay!nullary!0| b) b (not (select |ay!nullary!0| #x0))) false)))
    (check-sat)
"#;

#[test]
fn actual_unsafe_route_returns_original_checked_ground_derivation() {
    let problem = ChcParser::parse(UNSAFE).expect("unsafe source");
    let candidate = try_build_counterexample(&problem, Duration::from_secs(5))
        .expect("real array witness, not Unknown or a vacuous candidate");
    assert!(candidate.cex.witness.is_none());
    let derivation = candidate
        .cex
        .ground_derivation
        .as_ref()
        .expect("ground evidence");
    assert_eq!(
        crate::ground_derivation::validate_ground_derivation(&problem, derivation),
        Ok(())
    );
    assert!(validate_counterexample(
        &problem,
        &candidate.cex,
        Duration::from_secs(5),
        false
    ));
}

#[test]
fn actual_safe_twin_never_publishes_a_marker_counterexample_and_is_safe() {
    let safe = UNSAFE.replace(
        "(not (select |ay!nullary!0| #x0))",
        "(select |ay!nullary!0| #x0)",
    );
    let problem = ChcParser::parse(&safe).expect("safe source");
    assert!(try_build_counterexample(&problem, Duration::from_secs(5)).is_err());
    let result = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig::with_budget(Duration::from_secs(10), false),
    )
    .solve();
    assert!(
        matches!(result, VerifiedChcResult::Safe(_)),
        "actual Safe twin: {result:?}"
    );
}

#[test]
fn real_executor_decides_both_generated_array_obligations() {
    for (source, expected_sat) in [
        (UNSAFE.to_string(), true),
        (
            UNSAFE.replace(
                "(not (select |ay!nullary!0| #x0))",
                "(select |ay!nullary!0| #x0)",
            ),
            false,
        ),
    ] {
        let problem = ChcParser::parse(&source).expect("source");
        let predicate = problem.clauses()[0].head.predicate_id().expect("fact head");
        let nodes = vec![MarkerDagNode {
            predicate,
            clause_idx: 0,
            children: Vec::new(),
        }];
        let control = Control::capture(Duration::from_secs(5)).expect("owner");
        let _scope = control.enter();
        let names = Names::capture(&problem, &nodes, 1, &control).expect("names");
        let formula =
            marker_dag_formula(&problem, 1, &nodes, 0, &names, &control).expect("formula");
        let result =
            marker_dag_raw_executor_model(&formula, control.remaining().expect("same end"));
        if expected_sat {
            assert!(matches!(result, SmtResult::Sat(_)), "real SAT: {result:?}");
        } else {
            assert!(matches!(result, SmtResult::Unsat), "real UNSAT: {result:?}");
        }
    }
}

#[test]
fn original_store_in_head_false_unsafe_shape_remains_safe() {
    let source = r#"
        (set-logic HORN)
        (declare-fun P ((Array (_ BitVec 4) Bool)) Bool)
        (assert (forall ((a (Array (_ BitVec 4) Bool)))
          (P (store a #x0 true))))
        (assert (forall ((b (Array (_ BitVec 4) Bool)))
          (=> (and (P b) (not (select b #x0))) false)))
        (check-sat)
    "#;
    let problem = ChcParser::parse(source).expect("original false-unsafe shape");
    assert!(try_build_counterexample(&problem, Duration::from_secs(5)).is_err());
    let result = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig::with_budget(Duration::from_secs(10), false),
    )
    .solve();
    assert!(
        matches!(result, VerifiedChcResult::Safe(_)),
        "store in original head: {result:?}"
    );
}
