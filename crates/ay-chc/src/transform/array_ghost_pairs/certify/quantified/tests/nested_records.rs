// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

// Source-derived CHC layout, not the distinct six-field BMC MIR layout.
// The group deliberately places the outer declaration before its dependency.
fn source(fill: bool) -> QuantifiedChcProblem {
    let matrix = if fill {
        "(and
          (=> (bvult i old)
            (= (select (fld_data (fld_vec w)) i) (select (fld_data v) i)))
          (=> (and (bvuge i old) (bvult i new))
            (= (select (fld_data (fld_vec w)) i) fill)))"
    } else {
        "(=> (bvult i old)
          (= (select (fld_data (fld_vec w)) i) (select (fld_data v) i)))"
    };
    QuantifiedChcProblem::parse_smtlib(&format!(
        "(set-logic HORN)
        (declare-datatypes ((MCVecIntoIter 0) (MCVec 0))
          (((mkIter (fld_vec MCVec) (fld_pos (_ BitVec 64))))
           ((mkVec (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64))
             (fld_cap (_ BitVec 64))
             (fld_data (Array (_ BitVec 64) (_ BitVec 8)))))))
        (declare-var v MCVec)(declare-var w MCVecIntoIter)
        (declare-var b (Array (_ BitVec 64) (_ BitVec 8)))
        (declare-var old (_ BitVec 64))(declare-var new (_ BitVec 64))
        (declare-var pos (_ BitVec 64))(declare-var fill (_ BitVec 8))
        (declare-rel P (MCVecIntoIter (_ BitVec 64) (_ BitVec 8)))
        (declare-rel error ())
        (rule (=> (and (= old (fld_len v)) (bvult old new)
          (= w (mkIter (mkVec (fld_ptr v) new (fld_cap v) b) pos))
          (forall ((i (_ BitVec 64))) {matrix})) (P w old fill)))
        (rule (=> (and (P w old fill)
          (bvuge (fld_pos w) old)
          (bvult (fld_pos w) (fld_len (fld_vec w)))
          (bvuge (fld_pos w) (_ bv32 64))
          (not (= (select (fld_data (fld_vec w)) (fld_pos w)) fill))) error))
        (query error)"
    ))
    .expect("complete source-derived nested iterator resize")
}

fn candidate(source: &QuantifiedChcProblem, control: &SourceControl<'_>) -> GhostSourceCertificate {
    let projection = RecordProjection::new(source, control).unwrap();
    let projected = projection.project(source, control).unwrap();
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
    assert_eq!(vars.len(), 9, "five iterator leaves, old/fill, ghost pair");
    let terms: Vec<_> = vars.iter().cloned().map(ChcExpr::var).collect();
    let formula = op(
        ChcOp::Implies,
        vec![
            ChcExpr::and_all(vec![
                op(ChcOp::BvUGe, vec![terms[7].clone(), terms[5].clone()]),
                op(ChcOp::BvULt, vec![terms[7].clone(), terms[1].clone()]),
                op(
                    ChcOp::BvUGe,
                    vec![terms[7].clone(), ChcExpr::BitVec(32, 64)],
                ),
            ]),
            ChcExpr::eq(terms[8].clone(), terms[6].clone()),
        ],
    );
    let mut model = InvariantModel::new();
    model.set(predicate.id, PredicateInterpretation::new(vars, formula));
    model.set(
        problem.predicates()[1].id,
        PredicateInterpretation::new(vec![], ChcExpr::Bool(false)),
    );
    GhostSourceCertificate {
        source: Arc::from(source.source_smtlib()),
        interpretation: GhostPairModel {
            spec,
            model,
            executor_term_memory_limit: Some(64 * 1024 * 1024),
        },
        records: Some(RecordSource {
            projection,
            projected,
        }),
    }
}

#[test]
fn nested_record_replay_retains_original_constructor_and_selector_paths() {
    let source = source(true);
    let token = CancellationToken::new();
    let certificate = candidate(&source, &SourceControl::new(deadline(), &token));
    let replay = certificate
        .replay_obligations(&source, deadline(), &token)
        .unwrap();
    assert_eq!(replay.len(), 3);
    let fact = &replay[0].smtlib;
    assert!(fact.contains("(MCVec 0)"));
    assert!(fact.contains("(MCVecIntoIter 0)"));
    assert!(fact.contains("(declare-const w MCVecIntoIter)"));
    assert!(fact.contains(
        "(= w ((as mkIter MCVecIntoIter) ((as mkVec MCVec) (fld_ptr v) new (fld_cap v) b) pos))"
    ));
    let premise = &source.premises()[0][0];
    assert!(fact.contains(&format!(
        "(assert (forall (({} (_ BitVec 64))) {}))",
        premise.binder().name,
        InvariantModel::expr_to_smtlib(premise.matrix())
    )));
    assert!(replay[1]
        .smtlib
        .contains("(select (fld_data ((as fld_vec MCVec) w)) (fld_pos w))"));
    for obligation in replay {
        assert!(!obligation.smtlib.contains("ay!record!"));
        assert!(!obligation.smtlib.contains("(declare-fun fld_vec"));
        assert!(!obligation.smtlib.contains("(declare-fun fld_data"));
    }
}

#[test]
fn nested_record_projection_is_bound_to_the_original_premise_source() {
    let source = source(true);
    let missing = self::source(false);
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let certificate = candidate(&source, &control);
    let projection = &certificate.records.as_ref().unwrap().projection;
    assert!(!projection.matches_source(&missing, &control));
    assert!(certificate
        .replay_obligations(&missing, deadline(), &token)
        .is_err());
    assert!(replay::prepare(
        &missing,
        &certificate.interpretation,
        0,
        &control,
        Some(projection)
    )
    .is_none());
}

#[test]
fn nested_record_candidate_requires_original_source_discharge() {
    let source = source(true);
    let missing = self::source(false);
    let token = CancellationToken::new();
    let certificate = candidate(&source, &SourceControl::new(deadline(), &token));
    assert!(certificate.recheck(&source, Instant::now() + Duration::from_secs(30), &token));
    let wrong = candidate(&missing, &SourceControl::new(deadline(), &token));
    assert!(!wrong.recheck(&missing, Instant::now() + Duration::from_secs(30), &token));
}

#[test]
fn public_nested_record_solve_synthesizes_then_rechecks_original_records() {
    use crate::quantified::QuantifiedChcResult;

    let source = source(true);
    let token = CancellationToken::new();
    let result = source.solve(Duration::from_secs(30), Some(64 * 1024 * 1024), &token);
    let QuantifiedChcResult::Safe(evidence) = result else {
        panic!("complete nested iterator resize should certify")
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
