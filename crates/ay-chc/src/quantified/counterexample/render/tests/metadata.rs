// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{ChcDtConstructor, ChcDtSelector, InvariantModel};

#[test]
fn fresh_names_reserve_unused_declarations_binders_and_unselected_clause_values() {
    let mut declarations = ChcProblem::new();
    declarations.declare_predicate("ay_qcex_0", vec![]);
    declarations.add_datatype_def(
        "ay_qcex_1".into(),
        vec![(
            "ay_qcex_2".into(),
            vec![("ay_qcex_3".into(), ChcSort::Bool)],
        )],
    );
    let query = |constraint| {
        HornClause::new(
            ClauseBody {
                predicates: vec![],
                constraint: Some(constraint),
            },
            ClauseHead::False,
        )
    };
    let source = QuantifiedChcProblem::new(
        declarations,
        vec![
            QuantifiedHornClause::new(query(var("x", ChcSort::Bool)), vec![]),
            QuantifiedHornClause::new(
                query(var("ay_qcex_5", ChcSort::Bool)),
                vec![UniversalPremise::new(
                    ChcVar::new("ay_qcex_4", ChcSort::BitVec(2)),
                    ChcExpr::Bool(true),
                )],
            ),
        ],
    )
    .unwrap();
    let script = output(&source, &[0]);
    // The private family deliberately avoids the frontend's reserved __ay_
    // prefix. It also cannot shadow names absent from this selected path.
    assert!(script.contains("(declare-const ay_qcex_6 Bool)"));
    assert_eq!(script.matches("(declare-const ").count(), 1);
    assert!(script.contains("ay_qcex_1"));
    assert!(script.contains("ay_qcex_2"));
    assert!(script.contains("ay_qcex_3"));
    assert!(!script.contains("__ay_"));
    assert!(!ay_frontend::is_source_reserved_symbol("ay_qcex_6"));
    assert!(ay_frontend::is_source_reserved_symbol("__ay_qcex_6"));
    ay_frontend::parse(&script).expect("ordinary unreserved generated names");
}

fn array(value: ChcSort) -> ChcSort {
    ChcSort::Array(Box::new(ChcSort::BitVec(2)), Box::new(value))
}

fn application(name: &str, sort: ChcSort, arguments: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::FuncApp(
        name.into(),
        sort,
        arguments.into_iter().map(Arc::new).collect(),
    )
}

#[test]
fn original_record_arrays_and_grouped_matrices_keep_full_quoted_declarations() {
    let cell = ChcSort::Datatype {
        name: "Cell record".into(),
        constructors: crate::ChcDtConstructors::new(vec![ChcDtConstructor {
            name: "mk cell".into(),
            selectors: vec![ChcDtSelector {
                name: "cell data".into(),
                sort: array(ChcSort::BitVec(2)),
            }],
        }]),
    };
    let mut declarations = ChcProblem::new();
    declarations.add_datatype_def(
        "Cell record".into(),
        vec![(
            "mk cell".into(),
            vec![("cell data".into(), array(ChcSort::BitVec(2)))],
        )],
    );
    declarations.add_datatype_def(
        "Unused record".into(),
        vec![(
            "mk unused".into(),
            vec![("unused field".into(), ChcSort::Bool)],
        )],
    );
    let records = var("records", array(cell.clone()));
    let fill = var("fill", ChcSort::BitVec(2));
    let constant = ChcExpr::ConstArray(
        ChcSort::BitVec(2),
        Arc::new(application(
            "mk cell",
            cell,
            vec![ChcExpr::ConstArray(
                ChcSort::BitVec(2),
                Arc::new(fill.clone()),
            )],
        )),
    );
    let constraint = eq(records.clone(), constant);
    let row = op(ChcOp::Select, vec![records, var("r", ChcSort::BitVec(2))]);
    let data = application("cell data", array(ChcSort::BitVec(2)), vec![row]);
    let matrix = eq(
        op(ChcOp::Select, vec![data, var("c", ChcSort::BitVec(2))]),
        fill,
    );
    let premise = UniversalPremise::with_binders(
        vec![
            ChcVar::new("r", ChcSort::BitVec(2)),
            ChcVar::new("c", ChcSort::BitVec(2)),
        ],
        matrix.clone(),
    )
    .unwrap();
    let source = QuantifiedChcProblem::new(
        declarations,
        vec![QuantifiedHornClause::new(
            HornClause::new(
                ClauseBody {
                    predicates: vec![],
                    constraint: Some(constraint.clone()),
                },
                ClauseHead::False,
            ),
            vec![premise],
        )],
    )
    .unwrap();
    let script = output(&source, &[0]);
    assert!(script.contains("((as const (Array (_ BitVec 2) |Cell record|))"));
    assert!(script.contains("|Unused record|"));
    assert!(script.contains("|mk unused|"));
    assert!(script.contains("|unused field|"));
    assert!(script.contains(&InvariantModel::expr_to_smtlib(&constraint)));
    assert!(script.contains(&InvariantModel::expr_to_smtlib(&matrix)));
    assert!(script.contains("(forall ((r (_ BitVec 2))(c (_ BitVec 2)))"));
    assert!(!script.contains("declare-fun"));
    ay_frontend::parse(&script).expect("complete typed record declarations and raw assertions");
}
