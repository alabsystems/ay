// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

fn source(fill: bool) -> QuantifiedChcProblem {
    let matrix = if fill {
        "(and (=> (bvult i old) (= (select (data w) i) (select (data v) i)))
          (=> (and (bvuge i old) (bvult i new)) (= (select (data w) i) fill)))"
    } else {
        "(=> (bvult i old) (= (select (data w) i) (select (data v) i)))"
    };
    QuantifiedChcProblem::parse_smtlib(&format!(
        "(set-logic HORN)
        (declare-datatype Vec ((mkVec (ptr (_ BitVec 64)) (len (_ BitVec 64))
          (cap (_ BitVec 64)) (data (Array (_ BitVec 64) (_ BitVec 8))))))
        (declare-var v Vec)(declare-var w Vec)
        (declare-var b (Array (_ BitVec 64) (_ BitVec 8)))
        (declare-var old (_ BitVec 64))(declare-var new (_ BitVec 64))
        (declare-var fill (_ BitVec 8))(declare-var j (_ BitVec 64))
        (declare-rel P (Vec (_ BitVec 64) (_ BitVec 8)))
        (declare-rel error ())
        (rule (=> (and (= old (len v)) (bvult old new)
          (= w (mkVec (ptr v) new (cap v) b))
          (forall ((i (_ BitVec 64))) {matrix})) (P w old fill)))
        (rule (=> (and (P w old fill) (bvuge j old) (bvult j (len w))
          (bvuge j (_ bv32 64)) (not (= (select (data w) j) fill))) error))
        (query error)"
    ))
    .expect("complete source-derived DT Vec resize")
}

fn record_candidate(projected: &QuantifiedChcProblem) -> GhostPairModel {
    let problem = projected.source_problem();
    let spec = GhostPairSpec::analyze(problem, 1);
    let predicate = &problem.predicates()[0];
    let vars: Vec<_> = spec
        .extended_sorts(predicate.id, &predicate.arg_sorts)
        .unwrap()
        .into_iter()
        .enumerate()
        .map(|(i, sort)| ChcVar::new(format!("m{i}"), sort))
        .collect();
    assert_eq!(
        vars.len(),
        8,
        "four Vec fields, old/fill, ghost index/value"
    );
    let terms: Vec<_> = vars.iter().cloned().map(ChcExpr::var).collect();
    let formula = op(
        ChcOp::Implies,
        vec![
            ChcExpr::and_all(vec![
                op(ChcOp::BvUGe, vec![terms[6].clone(), terms[4].clone()]),
                op(ChcOp::BvULt, vec![terms[6].clone(), terms[1].clone()]),
                op(
                    ChcOp::BvUGe,
                    vec![terms[6].clone(), ChcExpr::BitVec(32, 64)],
                ),
            ]),
            ChcExpr::eq(terms[7].clone(), terms[5].clone()),
        ],
    );
    let mut model = InvariantModel::new();
    model.set(predicate.id, PredicateInterpretation::new(vars, formula));
    model.set(
        problem.predicates()[1].id,
        PredicateInterpretation::new(vec![], ChcExpr::Bool(false)),
    );
    GhostPairModel {
        spec,
        model,
        executor_term_memory_limit: Some(64 * 1024 * 1024),
    }
}

fn candidate(source: &QuantifiedChcProblem, control: &SourceControl<'_>) -> GhostSourceCertificate {
    let projection = RecordProjection::new(source, control).unwrap();
    let projected = projection.project(source, control).unwrap();
    GhostSourceCertificate {
        source: Arc::from(source.source_smtlib()),
        interpretation: record_candidate(&projected),
        records: Some(RecordSource {
            projection,
            projected,
        }),
    }
}

#[test]
fn original_record_replay_keeps_datatypes_constructor_equality_and_forall() {
    let source = source(true);
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let certificate = candidate(&source, &control);
    let obligations = certificate
        .replay_obligations(&source, deadline(), &token)
        .unwrap();
    assert_eq!(obligations.len(), 3);
    let text = &obligations[0].smtlib;
    assert!(text.contains("(declare-datatypes"));
    assert!(text.contains("(declare-const w Vec)"));
    assert!(text.contains("(= w ((as mkVec Vec) (ptr v) new (cap v) b))"));
    let premise = &source.premises()[0][0];
    assert!(text.contains(&format!(
        "(assert (forall (({} (_ BitVec 64))) {}))",
        premise.binder().name,
        InvariantModel::expr_to_smtlib(premise.matrix())
    )));
    assert!(!text.contains("(declare-fun data"));
    assert!(obligations[1].smtlib.contains("(select (data w) j)"));
    assert!(obligations[1].smtlib.contains("(_ bv32 64)"));
    assert_eq!(
        obligations
            .iter()
            .map(|o| o.clause_index)
            .collect::<Vec<_>>(),
        vec![0, 1, 2]
    );
}

#[test]
fn record_source_cannot_use_a_nonprojected_model_or_projection_from_another_source() {
    let source = source(true);
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let certificate = candidate(&source, &control);
    assert!(replay::prepare(&source, &certificate.interpretation, 0, &control, None).is_none());
    let changed = self::source(false);
    let projection = &certificate.records.as_ref().unwrap().projection;
    assert!(replay::prepare(
        &changed,
        &certificate.interpretation,
        0,
        &control,
        Some(projection)
    )
    .is_none());
    assert!(certificate
        .replay_obligations(&changed, deadline(), &token)
        .is_err());
}

#[test]
fn cancelled_record_replay_is_sticky_across_token_reset() {
    let source = source(true);
    let token = CancellationToken::new();
    let live = SourceControl::new(deadline(), &token);
    let certificate = candidate(&source, &live);
    let stopped = SourceControl::new(deadline(), &token);
    token.cancel();
    let projection = &certificate.records.as_ref().unwrap().projection;
    assert!(replay::prepare(
        &source,
        &certificate.interpretation,
        0,
        &stopped,
        Some(projection)
    )
    .is_none());
    token.reset();
    assert!(replay::prepare(
        &source,
        &certificate.interpretation,
        0,
        &stopped,
        Some(projection)
    )
    .is_none());
    assert!(certificate
        .replay_obligations(&source, deadline(), &token)
        .is_ok());
}

#[test]
fn projected_candidate_still_needs_original_record_discharge() {
    let source = source(true);
    let missing = self::source(false);
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let certificate = candidate(&source, &control);
    assert!(certificate.recheck(&source, Instant::now() + Duration::from_secs(30), &token));
    let wrong = candidate(&missing, &SourceControl::new(deadline(), &token));
    assert!(!wrong.recheck(&missing, Instant::now() + Duration::from_secs(30), &token));
}

#[test]
fn public_record_solve_synthesizes_and_rechecks_without_a_supplied_model() {
    use crate::quantified::QuantifiedChcResult;

    let source = source(true);
    let token = CancellationToken::new();
    let result = source.solve(Duration::from_secs(30), Some(64 * 1024 * 1024), &token);
    let QuantifiedChcResult::Safe(evidence) = result else {
        panic!("source-derived complete Vec resize should certify")
    };
    assert_eq!(evidence.source_smtlib(), source.source_smtlib());
    assert_eq!(evidence.replay_obligations().len(), 3);
    assert!(evidence.recheck(&source, Duration::from_secs(30), &token));
    let missing = self::source(false);
    assert!(!matches!(
        missing.solve(Duration::from_secs(30), Some(64 * 1024 * 1024), &token),
        QuantifiedChcResult::Safe(_)
    ));
}
