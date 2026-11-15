// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;
use crate::quantified::QuantifiedChcFunction;
use std::collections::BTreeSet;

mod boundaries;

const SOURCE: &str = "(declare-datatype R ((mkR (flag Bool) (payload (_ BitVec 8))
            (data (Array (_ BitVec 136) (_ BitVec 8))))))
         (declare-fun F (Bool (_ BitVec 8)) (_ BitVec 8))
         (declare-fun G () (_ BitVec 8))
         (declare-fun ay!record!0 () (_ BitVec 136))
         (declare-fun ay!record!1 ((_ BitVec 136)) (_ BitVec 136))
         (declare-var r R)(declare-var n (_ BitVec 8))
         (declare-rel P (R (_ BitVec 8)))
         (rule (=> (and (= (F (flag r) (payload r)) G)
             (forall ((i (_ BitVec 8)) (j (_ BitVec 8)))
                 (= (F true i) (F true j)))) (P r (F true G))))
         (rule (=> (P r n)
             (P (mkR (flag r) (F false (payload r))
                   (store (data r) (_ bv0 136) G)) n)))
         (query (P r G))";

fn source_with_functions() -> QuantifiedChcProblem {
    QuantifiedChcProblem::parse_smtlib(SOURCE).unwrap()
}

fn app(name: &str, sort: ChcSort, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::FuncApp(
        name.to_owned(),
        sort,
        args.into_iter().map(Arc::new).collect(),
    )
}

#[test]
fn exact_projected_source_keeps_ordered_signatures_and_unused_global_declarations() {
    let original = source_with_functions();
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let projection = RecordProjection::new(&original, &control).unwrap();
    let projected = projection.project(&original, &control).unwrap();
    assert_eq!(
        projected.function_declarations(),
        original.function_declarations()
    );
    assert_eq!(
        projected
            .function_declarations()
            .iter()
            .map(|f| f.name())
            .collect::<Vec<_>>(),
        ["F", "G", "ay!record!0", "ay!record!1"]
    );
    assert!(projected.source_problem().datatype_defs().is_empty());
    assert_eq!(projected.source_problem().clauses().len(), 3);
    assert_eq!(
        projected.source_problem().clauses()[2].source_query_ordinal,
        Some(0)
    );
    assert!(projected.source_problem().is_fixedpoint_format());
    let source = projected.source_smtlib();
    let declarations = [
        "(declare-fun F (Bool (_ BitVec 8)) (_ BitVec 8))",
        "(declare-fun G () (_ BitVec 8))",
        "(declare-fun ay!record!0 () (_ BitVec 136))",
        "(declare-fun ay!record!1 ((_ BitVec 136)) (_ BitVec 136))",
    ];
    let mut previous = 0;
    for declaration in declarations {
        assert_eq!(source.matches(declaration).count(), 1);
        let index = source.find(declaration).unwrap();
        assert!(index >= previous);
        previous = index;
    }
}

#[test]
fn unused_function_names_reserve_fields_and_every_grouped_binder_without_uf_capture() {
    let original = source_with_functions();
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let projection = RecordProjection::new(&original, &control).unwrap();
    let projected = projection.project(&original, &control).unwrap();
    let ClauseHead::Predicate(_, args) = &projected.source_problem().clauses()[0].head else {
        panic!("fact head")
    };
    for (arg, expected) in args[..3]
        .iter()
        .zip(["ay!record!2", "ay!record!3", "ay!record!4"])
    {
        assert!(matches!(arg, ChcExpr::Var(var) if var.name == expected));
    }
    let group = &projected.premises()[0][0];
    let binders: Vec<_> = group.binders().collect();
    assert_eq!(binders.len(), 2);
    assert_eq!(binders[0].name, "ay!record!5");
    assert_eq!(binders[1].name, "ay!record!6");
    let ChcExpr::Op(ChcOp::Eq, sides) = group.matrix() else {
        panic!("matrix equality")
    };
    for (side, binder) in sides.iter().zip(binders) {
        assert!(
            matches!(side.as_ref(), ChcExpr::FuncApp(name, ChcSort::BitVec(8), actuals)
            if name == "F" && actuals[0].as_ref() == &ChcExpr::Bool(true)
            && actuals[1].as_ref() == &ChcExpr::Var(binder.clone()))
        );
    }
    assert_eq!(
        args[3],
        app(
            "F",
            ChcSort::BitVec(8),
            vec![ChcExpr::Bool(true), app("G", ChcSort::BitVec(8), vec![])]
        )
    );
}

#[test]
fn record_selectors_and_constructors_eliminate_exactly_while_global_calls_remain() {
    let original = source_with_functions();
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let projection = RecordProjection::new(&original, &control).unwrap();
    let projected = projection.project(&original, &control).unwrap();
    let clause = &projected.source_problem().clauses()[1];
    let fields = &clause.body.predicates[0].1;
    let ClauseHead::Predicate(_, head) = &clause.head else {
        panic!("transition head")
    };
    let ClauseHead::Predicate(id, actuals) = &original.source_problem().clauses()[1].head else {
        panic!("original head")
    };
    let ChcExpr::FuncApp(_, _, constructor_fields) = &actuals[0] else {
        panic!("original constructor")
    };
    let ChcExpr::Op(ChcOp::Store, store) = constructor_fields[2].as_ref() else {
        panic!("original store")
    };
    assert_eq!(head[0], fields[0]);
    assert_eq!(
        head[1],
        app(
            "F",
            ChcSort::BitVec(8),
            vec![ChcExpr::Bool(false), fields[1].clone()]
        )
    );
    assert_eq!(
        head[2],
        op(
            ChcOp::Store,
            vec![
                fields[2].clone(),
                store[1].as_ref().clone(),
                app("G", ChcSort::BitVec(8), vec![])
            ]
        )
    );
    assert_eq!(head[3], fields[3]);
    let replay = projection
        .project_arguments(*id, actuals, &control)
        .unwrap();
    for (leaf, name) in replay[..3].iter().zip(["flag", "payload", "data"]) {
        assert!(matches!(leaf, ChcExpr::FuncApp(actual_name, _, args)
            if actual_name == name && args[0].as_ref() == &actuals[0]));
    }
    assert_eq!(replay[3], actuals[1]);
}

#[test]
fn function_only_source_changes_invalidate_the_immutable_projection_identity() {
    let original = source_with_functions();
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let projection = RecordProjection::new(&original, &control).unwrap();
    for changed in [
        SOURCE.replace("ay!record!0", "unused-renamed"),
        SOURCE.replace(
            "(declare-fun ay!record!0 () (_ BitVec 136))",
            "(declare-fun ay!record!0 () (_ BitVec 135))",
        ),
    ] {
        let changed = QuantifiedChcProblem::parse_smtlib(&changed).unwrap();
        assert_ne!(
            original.function_declarations(),
            changed.function_declarations()
        );
        assert!(!projection.matches_source(&changed, &control));
        assert!(projection.project(&changed, &control).is_none());
    }
    assert!(projection.project(&original, &control).is_some());
}
