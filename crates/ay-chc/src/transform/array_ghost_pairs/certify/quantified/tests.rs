// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use crate::quantified::{QuantifiedHornClause, UniversalPremise};
use crate::{ChcOp, ChcSort, ChcVar, ClauseBody, PredicateInterpretation};

mod functions;
mod grouped;
mod namespace;
mod nested_records;
mod records;
mod resources;
mod wide_tables;

fn op(operator: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(operator, args.into_iter().map(Arc::new).collect())
}

fn variable(name: &str, sort: &ChcSort) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, sort.clone()))
}

pub(super) fn fixture(fill: bool, binder_name: &str) -> QuantifiedChcProblem {
    let index = ChcSort::BitVec(64);
    let cell = ChcSort::BitVec(8);
    let array = ChcSort::Array(Box::new(index.clone()), Box::new(cell.clone()));
    let mut declarations = ChcProblem::new();
    let pred = declarations.declare_predicate(
        "P",
        vec![array.clone(), index.clone(), index.clone(), cell.clone()],
    );
    let a = variable("a", &array);
    let b = variable("b", &array);
    let old = variable("old", &index);
    let new = variable("new", &index);
    let value = variable("fill", &cell);
    let binder = ChcVar::new(binder_name, index.clone());
    let i = ChcExpr::var(binder.clone());
    let prefix = op(
        ChcOp::Implies,
        vec![
            op(ChcOp::BvULt, vec![i.clone(), old.clone()]),
            ChcExpr::eq(
                ChcExpr::select(b.clone(), i.clone()),
                ChcExpr::select(a, i.clone()),
            ),
        ],
    );
    let suffix_guard = ChcExpr::and(
        op(ChcOp::BvUGe, vec![i.clone(), old.clone()]),
        op(ChcOp::BvULt, vec![i.clone(), new.clone()]),
    );
    let matrix = if fill {
        ChcExpr::and(
            prefix,
            op(
                ChcOp::Implies,
                vec![
                    suffix_guard,
                    ChcExpr::eq(ChcExpr::select(b.clone(), i), value.clone()),
                ],
            ),
        )
    } else {
        prefix
    };
    let args = vec![b.clone(), old.clone(), new.clone(), value.clone()];
    let fact = HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(pred, args.clone()),
    );
    let j = variable("j", &index);
    let guard = ChcExpr::and_all(vec![
        op(ChcOp::BvUGe, vec![j.clone(), old]),
        op(ChcOp::BvULt, vec![j.clone(), new]),
        op(ChcOp::BvUGe, vec![j.clone(), ChcExpr::BitVec(32, 64)]),
        ChcExpr::ne(ChcExpr::select(b, j), value),
    ]);
    let query = HornClause::new(
        ClauseBody::new(vec![(pred, args)], Some(guard)),
        ClauseHead::False,
    );
    QuantifiedChcProblem::new(
        declarations,
        vec![
            QuantifiedHornClause::new(fact, vec![UniversalPremise::new(binder, matrix)]),
            QuantifiedHornClause::new(query, vec![]),
        ],
    )
    .expect("bounded original symbolic resize source")
}

pub(super) fn interpretation(problem: &QuantifiedChcProblem) -> GhostPairModel {
    let source = problem.source_problem();
    let pred = &source.predicates()[0];
    let spec = GhostPairSpec::analyze(source, 1);
    let sorts = spec.extended_sorts(pred.id, &pred.arg_sorts).unwrap();
    let vars: Vec<_> = sorts
        .into_iter()
        .enumerate()
        .map(|(i, sort)| ChcVar::new(format!("m{i}"), sort))
        .collect();
    let terms: Vec<_> = vars.iter().cloned().map(ChcExpr::var).collect();
    let guard = ChcExpr::and_all(vec![
        op(ChcOp::BvUGe, vec![terms[4].clone(), terms[1].clone()]),
        op(ChcOp::BvULt, vec![terms[4].clone(), terms[2].clone()]),
        op(
            ChcOp::BvUGe,
            vec![terms[4].clone(), ChcExpr::BitVec(32, 64)],
        ),
    ]);
    let formula = op(
        ChcOp::Implies,
        vec![guard, ChcExpr::eq(terms[5].clone(), terms[3].clone())],
    );
    let mut model = InvariantModel::new();
    model.set(pred.id, PredicateInterpretation::new(vars, formula));
    GhostPairModel {
        spec,
        model,
        executor_term_memory_limit: Some(64 * 1024 * 1024),
    }
}

pub(super) fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

#[test]
fn symbolic_source_uses_the_same_arbitrary_head_probe_not_low_index_enumeration() {
    let source = fixture(true, "i");
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let spec = GhostPairSpec::analyze(source.source_problem(), 1);
    let raw = rewrite_source(&source, &spec, &control).unwrap();
    let ClauseHead::Predicate(_, args) = &raw.clauses()[0].head else {
        panic!("fact head")
    };
    let probe = &args[4];
    assert!(
        matches!(probe, ChcExpr::Var(_)),
        "arbitrary BV64 head probe"
    );
    let expected =
        source_premises::instances(&source.premises()[0], std::slice::from_ref(probe), &control)
            .unwrap();
    let clause_text =
        InvariantModel::expr_to_smtlib(raw.clauses()[0].body.constraint.as_ref().unwrap());
    let ChcExpr::Op(ChcOp::And, conjuncts) = &expected[0] else {
        panic!("prefix and suffix instances")
    };
    for conjunct in conjuncts {
        assert!(clause_text.contains(&InvariantModel::expr_to_smtlib(conjunct)));
    }
    assert!(clause_text.contains("bvult") && clause_text.contains("bvuge"));
    assert!(!clause_text.contains("(_ bv31 64)"));
    assert!(raw.clauses()[1]
        .body
        .constraint
        .as_ref()
        .unwrap()
        .vars()
        .iter()
        .any(|v| v.name == "j"));
}

#[test]
fn full_original_replay_retains_universal_matrix_and_declares_its_free_array() {
    let source = fixture(true, "i");
    let model = interpretation(&source);
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    assert!(validate_interpretation(
        source.source_problem(),
        &model,
        || control.poll().is_none()
    ));
    let prepared = replay::prepare(&source, &model, 0, &control, None).unwrap();
    let matrix = InvariantModel::expr_to_smtlib(source.premises()[0][0].matrix());
    assert!(prepared
        .obligation
        .smtlib
        .contains(&format!("(assert (forall ((i (_ BitVec 64))) {matrix}))")));
    assert!(prepared
        .obligation
        .smtlib
        .contains("(declare-const a (Array (_ BitVec 64) (_ BitVec 8)))"));
    assert!(!prepared.obligation.smtlib.contains("(declare-const i "));
    assert_eq!(prepared.obligation.clause_index, 0);
    assert!(prepared.obligation.smtlib.ends_with("(check-sat)\n"));
}

#[test]
fn source_binder_and_free_names_cannot_capture_generated_ghosts_or_skolems() {
    let source = fixture(true, "__gpi0");
    let model = interpretation(&source);
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let raw = rewrite_source(&source, &model.spec, &control).unwrap();
    let ClauseHead::Predicate(_, args) = &raw.clauses()[0].head else {
        panic!("head")
    };
    assert!(matches!(&args[4], ChcExpr::Var(var) if var.name != "__gpi0"));
    let skolem_collision = fixture(true, "__gpc0");
    let prepared = replay::prepare(
        &skolem_collision,
        &interpretation(&skolem_collision),
        0,
        &control,
        None,
    )
    .unwrap();
    assert!(!prepared
        .obligation
        .smtlib
        .contains("(declare-const __gpc0 "));
    assert!(prepared
        .obligation
        .smtlib
        .contains("(forall ((__gpc0 (_ BitVec 64)))"));
}

#[test]
fn changed_source_premise_cannot_replay_or_recheck_even_identical_skeleton() {
    let source = fixture(true, "i");
    // Deliberately unsealed test-only state: identity refusal must precede SMT.
    let certificate = GhostSourceCertificate {
        source: Arc::from(source.source_smtlib()),
        interpretation: interpretation(&source),
        records: None,
    };
    let changed = fixture(false, "i");
    let token = CancellationToken::new();
    assert!(certificate
        .replay_obligations(&changed, deadline(), &token)
        .is_err());
    assert!(!certificate.recheck(&changed, deadline(), &token));
    let original = certificate
        .replay_obligations(&source, deadline(), &token)
        .unwrap();
    assert_eq!(original.len(), 2);
    assert!(original[1].smtlib.contains("(_ bv32 64)"));
}
