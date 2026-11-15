// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::ground_derivation::validate_ground_derivation;
use crate::{
    validate_chc_ground_derivation_artifact, validate_chc_ground_derivation_artifact_v2,
    ChcBmcUnsafeTraceAssignmentCompletenessReason, ChcParser, ChcPdrProofRun, ClauseBody,
    HornClause, PdrConfig, PdrSolver, VerifiedChcResult, VerifiedCounterexample,
};
use num_bigint::{BigInt, BigUint};
use num_rational::BigRational;
use std::sync::Arc;

const SMALL_BV8_SOURCE: &str = "(set-logic HORN)
(declare-fun P ((_ BitVec 8)) Bool)
(assert (P #x07))
(assert (forall ((x (_ BitVec 8)))
  (=> (and (P x) (= x #x07)) false)))
(check-sat)
";

fn one_state_counterexample(problem: &ChcProblem, value: SmtValue) -> Counterexample {
    let trace = LinearTrace {
        predicate: problem.predicates()[0].id,
        states: vec![vec![Some(value)]],
        edges: vec![super::super::TraceEdgeHint::default(); 2],
    };
    counterexample_from_linear_trace(problem, &trace, None, &CancellationToken::new())
        .expect("fact and query ground-validate on the original clauses")
}

fn bitvector_problem(width: u32, value: &SmtValue) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let sort = ChcSort::BitVec(width);
    let p = problem.declare_predicate("P", vec![sort.clone()]);
    let x = ChcExpr::var(ChcVar::new("x", sort));
    let literal = value
        .bitvec_to_chc_expr()
        .expect("canonical concrete bitvector");
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(p, vec![literal.clone()]),
    ));
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(p, vec![x.clone()])],
        Some(ChcExpr::eq(x, literal)),
    )));
    problem
}

fn confirmed_run(problem: &ChcProblem, candidate: Counterexample) -> ChcPdrProofRun {
    let mut config = PdrConfig::default();
    config.preserve_original_clauses = true;
    config.disable_array_scalarization = true;
    config.disable_cex_replay = true;
    config.strict_proofs = true;
    let confirmed = PdrSolver::new(problem.clone(), config)
        .confirm_counterexample(candidate)
        .expect("the publication verifier confirms this original ground derivation");
    ChcPdrProofRun::new(
        problem.clone(),
        VerifiedChcResult::Unsafe(VerifiedCounterexample::from_validated(confirmed)),
        "bmc",
    )
}

#[test]
fn bv8_linear_trace_retains_the_supported_value_through_consumer_evidence() {
    let problem = ChcParser::parse(SMALL_BV8_SOURCE).expect("exact small regression parses");
    let value = SmtValue::BitVec(7, 8);
    let candidate = one_state_counterexample(&problem, value.clone());
    let derivation = candidate
        .ground_derivation
        .as_ref()
        .expect("rich ground evidence");
    validate_ground_derivation(&problem, derivation).expect("revalidated source proof");
    assert_eq!(candidate.steps.len(), 1);
    assert_eq!(candidate.steps[0].assignments.get("__p0_a0"), Some(&7));
    assert_eq!(candidate.steps[0].clause_index, Some(0));
    let witness = candidate.witness.as_ref().expect("rich witness retained");
    assert_eq!(witness.entries[0].instances.get("__p0_a0"), Some(&value));
    assert_eq!(derivation.steps[1].env.get("x"), Some(&value));

    let run = confirmed_run(&problem, candidate);
    let evidence = run.consumer_evidence();
    let trace = evidence.unsafe_trace().expect("unsafe scalar trace");
    assert_eq!(trace.step_count, 1);
    assert_eq!(trace.steps[0].assignments.len(), 1);
    let assignment = &trace.steps[0].assignments[0];
    assert_eq!(assignment.predicate_argument_index, Some(0));
    assert_eq!(assignment.sort.as_deref(), Some("BitVec(8)"));
    assert_eq!(assignment.value, 7);
    assert_eq!(
        evidence
            .bmc_unsafe_trace_assignment_completeness(1, 1)
            .reason,
        ChcBmcUnsafeTraceAssignmentCompletenessReason::Complete
    );
    let json = evidence.to_json_value();
    assert_eq!(
        json["unsafe_trace_assignment_contract"]["schema_version"],
        1
    );
    assert_eq!(
        json["unsafe_trace"]["steps"][0]["assignments"][0]["value"],
        7
    );
}

#[test]
fn fitting_unsigned_values_survive_both_canonical_bitvector_representations() {
    for (width, raw) in [
        (1, 0),
        (1, 1),
        (8, 255),
        (63, i64::MAX as u128),
        (64, i64::MAX as u128),
        (128, 7),
        (129, 7),
        (136, 7),
        (crate::MAX_BITVECTOR_WIDTH, 7),
    ] {
        let value = SmtValue::try_bitvec_from_u128(raw, width).expect("canonical BV input");
        assert_eq!(
            scalar_assignment(&value, &ChcSort::BitVec(width)),
            i64::try_from(raw).ok()
        );
    }
}

#[test]
fn over_i64_bitvectors_are_omitted_instead_of_truncated_or_signed() {
    for (width, raw) in [
        (64, BigUint::from(1u8) << 63usize),
        (128, BigUint::from(u128::MAX)),
        (136, (BigUint::from(1u8) << 135usize) + BigUint::from(7u8)),
    ] {
        let value = SmtValue::try_bitvec_from_biguint(raw, width).expect("canonical BV input");
        assert_eq!(scalar_assignment(&value, &ChcSort::BitVec(width)), None);
    }
}

#[test]
fn malformed_widths_representations_and_source_sort_mismatches_never_normalize() {
    let cases = [
        (SmtValue::BitVec(256, 8), ChcSort::BitVec(8)),
        (SmtValue::BitVec(7, 0), ChcSort::BitVec(0)),
        (SmtValue::BitVec(7, 129), ChcSort::BitVec(129)),
        (SmtValue::BitVec(7, 8), ChcSort::BitVec(16)),
        (SmtValue::BitVec(7, 8), ChcSort::Int),
        (
            SmtValue::BigBitVec(Arc::new(BigUint::from(7u8)), 8),
            ChcSort::BitVec(8),
        ),
        (
            SmtValue::BigBitVec(Arc::new(BigUint::from(1u8) << 136usize), 136),
            ChcSort::BitVec(136),
        ),
        (
            SmtValue::BigBitVec(Arc::new(BigUint::from(7u8)), crate::MAX_BITVECTOR_WIDTH + 1),
            ChcSort::BitVec(crate::MAX_BITVECTOR_WIDTH + 1),
        ),
    ];
    for (value, sort) in cases {
        assert_eq!(scalar_assignment(&value, &sort), None);
    }
}

#[test]
fn existing_int_bool_and_explicit_unsupported_rich_cases_keep_their_contract() {
    for raw in [i64::MIN, 0, i64::MAX] {
        assert_eq!(
            scalar_assignment(&SmtValue::Int(i128::from(raw)), &ChcSort::Int),
            Some(raw)
        );
    }
    for raw in [i128::from(i64::MIN) - 1, i128::from(i64::MAX) + 1] {
        assert_eq!(scalar_assignment(&SmtValue::Int(raw), &ChcSort::Int), None);
    }
    for value in [false, true] {
        assert_eq!(
            scalar_assignment(&SmtValue::Bool(value), &ChcSort::Bool),
            Some(i64::from(value))
        );
    }
    let real = SmtValue::Real(BigRational::from_integer(BigInt::from(7)));
    assert_eq!(scalar_assignment(&real, &ChcSort::Real), None);
    let big = SmtValue::int_from_bigint(BigInt::from(i128::MAX) + BigInt::from(1));
    assert_eq!(scalar_assignment(&big, &ChcSort::Int), None);
    let array = SmtValue::ConstArray(Box::new(SmtValue::Bool(false)));
    assert_eq!(
        scalar_assignment(
            &array,
            &ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Bool))
        ),
        None
    );
}

#[test]
fn wide_small_value_is_present_in_the_original_ground_trace_and_scalar_row() {
    let value = SmtValue::try_bitvec_from_u128(7, 136).expect("canonical wide BV");
    let problem = bitvector_problem(136, &value);
    let candidate = one_state_counterexample(&problem, value.clone());
    assert_eq!(candidate.steps[0].assignments.get("__p0_a0"), Some(&7));
    assert_eq!(
        candidate.witness.as_ref().unwrap().entries[0]
            .instances
            .get("__p0_a0"),
        Some(&value)
    );
    validate_ground_derivation(&problem, candidate.ground_derivation.as_ref().unwrap()).unwrap();
    let run = confirmed_run(&problem, candidate);
    let evidence = run.consumer_evidence();
    assert_eq!(
        evidence.unsafe_trace().unwrap().steps[0].assignments[0]
            .sort
            .as_deref(),
        Some("BitVec(136)")
    );
    assert_eq!(
        evidence
            .bmc_unsafe_trace_assignment_completeness(1, 1)
            .reason,
        ChcBmcUnsafeTraceAssignmentCompletenessReason::Complete
    );
}

#[test]
fn omitted_large_value_retains_exact_v1_v2_ground_artifacts_and_fails_scalar_completeness() {
    let raw = (BigUint::from(1u8) << 135usize) + BigUint::from(7u8);
    let value = SmtValue::try_bitvec_from_biguint(raw, 136).unwrap();
    let problem = bitvector_problem(136, &value);
    let candidate = one_state_counterexample(&problem, value.clone());
    assert!(candidate.steps[0].assignments.is_empty());
    assert_eq!(
        candidate.witness.as_ref().unwrap().entries[0]
            .instances
            .get("__p0_a0"),
        Some(&value)
    );
    let v1 = candidate
        .ground_derivation_artifact(&problem)
        .expect("rich v1 evidence remains available");
    let v2 = candidate
        .ground_derivation_artifact_v2(&problem)
        .expect("rich v2 evidence remains available");
    let first = validate_chc_ground_derivation_artifact(&problem, v1.bytes()).unwrap();
    let second = validate_chc_ground_derivation_artifact_v2(&problem, v2.bytes()).unwrap();
    for snapshot in [first, second] {
        assert_eq!(snapshot.step_count(), 2);
        assert_eq!(snapshot.query_step(), 1);
        assert_eq!(snapshot.step(1).unwrap().source_binding("x"), Some(&value));
    }
    let run = confirmed_run(&problem, candidate);
    let completeness = run
        .consumer_evidence()
        .bmc_unsafe_trace_assignment_completeness(1, 1);
    assert_eq!(
        completeness.reason,
        ChcBmcUnsafeTraceAssignmentCompletenessReason::IncompletePredicateArgumentAssignments
    );
    assert!(!completeness.accepted_for_consumer);
    assert!(completeness.fail_closed);
}

#[test]
fn the_same_bv_assignment_does_not_validate_an_altered_original_query() {
    let original = ChcParser::parse(SMALL_BV8_SOURCE).unwrap();
    let candidate = one_state_counterexample(&original, SmtValue::BitVec(7, 8));
    let altered = ChcParser::parse(&SMALL_BV8_SOURCE.replace("(= x #x07)", "(= x #x08)")).unwrap();
    assert!(
        validate_ground_derivation(&altered, candidate.ground_derivation.as_ref().unwrap())
            .is_err()
    );
}
