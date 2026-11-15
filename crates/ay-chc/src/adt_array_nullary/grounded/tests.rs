// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::ground_derivation::validate_ground_derivation;
use crate::{ChcParser, ChcSort};
use std::time::Duration;

fn fixture() -> (ChcProblem, Vec<MarkerDagNode>, Names, Control) {
    let problem = ChcParser::parse(
        r#"
        (set-logic HORN)
        (declare-fun P ((Array (_ BitVec 4) Bool) Bool) Bool)
        (assert (P ((as const (Array (_ BitVec 4) Bool)) false) true))
        (assert (forall ((a (Array (_ BitVec 4) Bool)) (b Bool))
          (=> (and (P a b) b (not (select a #x0))) false)))
        (check-sat)
    "#,
    )
    .expect("source clauses");
    let predicate = problem.clauses()[0].head.predicate_id().expect("head");
    let nodes = vec![MarkerDagNode {
        predicate,
        clause_idx: 0,
        children: Vec::new(),
    }];
    let control = Control::capture(Duration::from_secs(10)).expect("owner");
    let names = Names::capture(&problem, &nodes, 1, &control).expect("names");
    (problem, nodes, names, control)
}

fn model(names: &Names, bad_array: bool) -> DetHashMap<String, SmtValue> {
    names
        .query()
        .values()
        .map(|replacement| {
            let ChcExpr::Var(var) = replacement else {
                unreachable!()
            };
            let value = match &var.sort {
                ChcSort::Bool => SmtValue::Bool(true),
                ChcSort::Array(_, _) => SmtValue::ConstArray(Box::new(SmtValue::Bool(bad_array))),
                other => panic!("unexpected fixture sort: {other:?}"),
            };
            (var.name.clone(), value)
        })
        .collect()
}

#[test]
fn original_array_and_query_bindings_produce_real_ground_evidence() {
    let (problem, nodes, names, control) = fixture();
    let candidate = from_model(
        &problem,
        1,
        &nodes,
        0,
        &names,
        &model(&names, false),
        &control,
    )
    .expect("complete original derivation");
    assert!(
        candidate.witness.is_none(),
        "never bypass vacuity using a cosmetic state"
    );
    let derivation = candidate
        .ground_derivation
        .as_ref()
        .expect("actual evidence");
    assert_eq!(derivation.steps.len(), 2);
    assert_eq!(derivation.steps[1].clause_index, 1);
    assert_eq!(derivation.steps[1].premises, vec![0]);
    assert_eq!(validate_ground_derivation(&problem, derivation), Ok(()));
    assert!(super::super::validate_counterexample(
        &problem,
        &candidate,
        Duration::from_secs(5),
        false
    ));
}

#[test]
fn wrong_array_or_missing_query_value_never_becomes_a_counterexample() {
    let (problem, nodes, names, control) = fixture();
    assert!(from_model(
        &problem,
        1,
        &nodes,
        0,
        &names,
        &model(&names, true),
        &control
    )
    .is_none());
    let mut partial = model(&names, false);
    let missing = partial.keys().next().expect("query value").clone();
    partial.remove(&missing);
    assert!(from_model(&problem, 1, &nodes, 0, &names, &partial, &control).is_none());
}

#[test]
fn original_safe_twin_rejects_the_same_otherwise_valid_model() {
    let (mut problem, nodes, names, control) = fixture();
    // The very same state is reachable, but the query now demands its opposite.
    let original = problem.clauses()[1].clone();
    let constraint = original.body.constraint.as_ref().expect("bad condition");
    let mut safe = original.clone();
    safe.body.constraint = Some(ChcExpr::not(constraint.clone()));
    problem.clauses_mut()[1] = safe;
    assert!(from_model(
        &problem,
        1,
        &nodes,
        0,
        &names,
        &model(&names, false),
        &control
    )
    .is_none());
}

#[test]
fn cyclic_premise_edge_is_rejected_independently() {
    let (problem, mut nodes, names, control) = fixture();
    nodes[0].children.push(0);
    assert!(from_model(
        &problem,
        1,
        &nodes,
        0,
        &names,
        &model(&names, false),
        &control
    )
    .is_none());
}

#[test]
fn changed_original_fact_cannot_reuse_an_old_array_model() {
    let (mut problem, nodes, names, control) = fixture();
    let crate::ClauseHead::Predicate(_, arguments) = &mut problem.clauses_mut()[0].head else {
        unreachable!()
    };
    arguments[0] = ChcExpr::const_array(ChcSort::BitVec(4), ChcExpr::Bool(true));
    assert!(from_model(
        &problem,
        1,
        &nodes,
        0,
        &names,
        &model(&names, false),
        &control,
    )
    .is_none());
}

#[test]
fn original_stop_before_ground_replay_cannot_publish_a_valid_candidate() {
    let (problem, nodes, names, control) = fixture();
    assert!(control.refuse::<()>().is_none());
    assert!(from_model(
        &problem,
        1,
        &nodes,
        0,
        &names,
        &model(&names, false),
        &control
    )
    .is_none());
}

#[test]
fn opaque_array_is_not_replaced_by_a_fabricated_default() {
    let (problem, nodes, names, control) = fixture();
    let mut values = model(&names, false);
    for replacement in names.query().values() {
        let ChcExpr::Var(var) = replacement else {
            unreachable!()
        };
        if matches!(var.sort, ChcSort::Array(_, _)) {
            values.insert(var.name.clone(), SmtValue::Opaque("@array".into()));
        }
    }
    assert!(from_model(&problem, 1, &nodes, 0, &names, &values, &control).is_none());
}

#[test]
fn exact_scalar_uf_observations_survive_original_name_pullback() {
    use crate::expr::evaluate::{
        uf_application_concrete_model_key, UF_APPLICATION_MODEL_MARKER_KEY,
        UF_APPLICATION_MODEL_MARKER_VALUE,
    };
    let problem = ChcParser::parse(
        r#"
        (set-logic HORN)
        (declare-fun f (Bool) (_ BitVec 8))
        (declare-fun P (Bool) Bool)
        (assert (forall ((x Bool)) (=> (= (f x) #x00) (P x))))
        (assert (forall ((q Bool)) (=> (and (P q) q) false)))
        (check-sat)
    "#,
    )
    .expect("UF source");
    let predicate = problem.clauses()[0].head.predicate_id().expect("fact");
    let nodes = vec![MarkerDagNode {
        predicate,
        clause_idx: 0,
        children: Vec::new(),
    }];
    let control = Control::capture(Duration::from_secs(5)).expect("owner");
    let names = Names::capture(&problem, &nodes, 1, &control).expect("names");
    let mut values: DetHashMap<_, _> = names
        .node(0)
        .expect("fact")
        .values()
        .chain(names.query().values())
        .map(|expression| {
            let ChcExpr::Var(var) = expression else {
                unreachable!()
            };
            (var.name.clone(), SmtValue::Bool(true))
        })
        .collect();
    let application = ChcExpr::FuncApp(
        "f".into(),
        ChcSort::BitVec(8),
        vec![std::sync::Arc::new(ChcExpr::Bool(true))],
    );
    let key = uf_application_concrete_model_key(&application, &[SmtValue::Bool(true)])
        .expect("concrete UF key");
    values.insert(
        UF_APPLICATION_MODEL_MARKER_KEY.into(),
        SmtValue::Opaque(UF_APPLICATION_MODEL_MARKER_VALUE.into()),
    );
    values.insert(key.clone(), SmtValue::BitVec(0, 8));
    assert!(from_model(&problem, 1, &nodes, 0, &names, &values, &control).is_some());
    values.insert(key, SmtValue::BitVec(1, 8));
    assert!(from_model(&problem, 1, &nodes, 0, &names, &values, &control).is_none());
}

fn repeated_array_head() -> (ChcProblem, GroundDerivation, PredicateId) {
    let array = "(Array (_ BitVec 8) Bool)";
    let sorts = std::iter::repeat_n(array, 8).collect::<Vec<_>>().join(" ");
    let variables = (0..8)
        .map(|i| format!("(v{i} {array})"))
        .collect::<Vec<_>>()
        .join(" ");
    let arguments = (0..8)
        .map(|i| format!("v{i}"))
        .collect::<Vec<_>>()
        .join(" ");
    let source = format!(
        "(set-logic HORN) (declare-fun P ({sorts}) Bool) (declare-fun Q ({array}) Bool)
         (assert (forall ((a {array})) (P a a a a a a a a)))
         (assert (forall ({variables}) (=> (P {arguments}) (Q v0))))
         (assert (forall ((q {array})) (=> (Q q) false))) (check-sat)"
    );
    let problem = ChcParser::parse(&source).expect("repeated original heads");
    let value = SmtValue::ArrayMap {
        default: Box::new(SmtValue::Bool(false)),
        entries: (0..32)
            .map(|i| (SmtValue::BitVec(i, 8), SmtValue::Bool(true)))
            .collect(),
    };
    let steps = vec![
        GroundDerivationStep {
            clause_index: 0,
            env: [("a".into(), value.clone())].into_iter().collect(),
            premises: vec![],
        },
        GroundDerivationStep {
            clause_index: 1,
            env: (0..8).map(|i| (format!("v{i}"), value.clone())).collect(),
            premises: vec![0],
        },
        GroundDerivationStep {
            clause_index: 2,
            env: [("q".into(), value)].into_iter().collect(),
            premises: vec![1],
        },
    ];
    let predicate = problem.clauses()[1].head.predicate_id().expect("root");
    (
        problem,
        GroundDerivation {
            steps,
            query_step: 2,
        },
        predicate,
    )
}

#[test]
fn repeated_array_head_copies_refuse_small_original_memory_before_presentation() {
    let (problem, derivation, _) = repeated_array_head();
    assert_eq!(validate_ground_derivation(&problem, &derivation), Ok(()));
    let _memory = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(512 * 1024));
    let control = Control::capture(Duration::from_secs(5)).expect("original memory owner");
    assert!(admit_presentation(&problem, &derivation, &control).is_none());
    assert!(
        control.poll().is_none(),
        "observed allocation refusal is terminal"
    );
}

#[test]
fn repeated_array_head_with_memory_keeps_full_trace_and_original_ground_evidence() {
    let (problem, derivation, predicate) = repeated_array_head();
    let _memory = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(32 * 1024 * 1024));
    let control = Control::capture(Duration::from_secs(5)).expect("original memory owner");
    let candidate = publish(&problem, derivation.clone(), predicate, 1, &control)
        .expect("adequately admitted presentation");
    assert_eq!(
        candidate.steps.len(),
        2,
        "the full linear derivation is restated"
    );
    assert_eq!(candidate.steps[0].clause_index, Some(0));
    assert_eq!(candidate.steps[1].clause_index, Some(1));
    let preserved = candidate
        .ground_derivation
        .as_ref()
        .expect("ground evidence");
    assert_eq!(preserved.query_step, derivation.query_step);
    assert_eq!(preserved.steps.len(), derivation.steps.len());
    for (actual, original) in preserved.steps.iter().zip(&derivation.steps) {
        assert_eq!(actual.clause_index, original.clause_index);
        assert_eq!(actual.premises, original.premises);
        assert_eq!(actual.env, original.env);
    }
    assert!(candidate.witness.is_none());
}

#[test]
fn compound_and_literal_array_heads_are_not_free_without_model_bindings() {
    let mut literal = ChcExpr::Bool(false);
    for _ in 0..16 {
        literal = ChcExpr::const_array(ChcSort::BitVec(8), literal);
    }
    let _memory = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(32 * 1024));
    let control = Control::capture(Duration::from_secs(5)).expect("original owner");
    assert!(admit_head(&literal, &DetHashMap::default(), &control).is_none());
    assert!(control.poll().is_none());
}

#[test]
fn expanding_bitvector_heads_reserve_declared_output_width_and_still_evaluate() {
    use crate::ChcOp;
    use std::sync::Arc;
    let width = crate::MAX_BITVECTOR_WIDTH;
    let expressions = [
        ChcExpr::Op(ChcOp::Int2Bv(width), vec![Arc::new(ChcExpr::Int(-1))]),
        ChcExpr::Op(
            ChcOp::BvZeroExtend(width - 1),
            vec![Arc::new(ChcExpr::BitVec(1, 1))],
        ),
        ChcExpr::Op(
            ChcOp::BvSignExtend(width - 1),
            vec![Arc::new(ChcExpr::BitVec(1, 1))],
        ),
        ChcExpr::Op(
            ChcOp::BvRepeat(32),
            vec![Arc::new(ChcExpr::BitVec(1, width / 32))],
        ),
    ];
    let env = DetHashMap::default();
    for expression in expressions {
        {
            let _memory = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(64 * 1024));
            let control = Control::capture(Duration::from_secs(5)).expect("small owner");
            assert!(admit_head(&expression, &env, &control).is_none());
            assert!(control.poll().is_none());
        }
        let _memory =
            crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(32 * 1024 * 1024));
        let control = Control::capture(Duration::from_secs(5)).expect("adequate owner");
        assert!(admit_head(&expression, &env, &control).is_some());
        let value = crate::ground_derivation::eval_ground_pub(&expression, &env)
            .expect("declared-width result really evaluates");
        let (bits, actual_width) = value.bitvec_to_biguint().expect("concrete BV");
        assert_eq!(actual_width, width);
        assert!(bits.bits() > 0);
        assert!(control.poll().is_some());
    }
}
