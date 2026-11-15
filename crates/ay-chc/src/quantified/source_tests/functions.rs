// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
#![allow(clippy::unwrap_used)]

use super::*;

fn function(name: &str, args: Vec<ChcSort>, result: ChcSort) -> QuantifiedChcFunction {
    QuantifiedChcFunction::new(name.into(), args, result)
}

fn call(name: &str, sort: ChcSort, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::FuncApp(name.into(), sort, args.into_iter().map(Arc::new).collect())
}

fn source(
    functions: Vec<QuantifiedChcFunction>,
    rows: Vec<QuantifiedHornClause>,
) -> ChcResult<QuantifiedChcProblem> {
    QuantifiedChcProblem::new_with_functions(ChcProblem::new(), functions, rows)
}

fn eq(left: ChcExpr, right: ChcExpr) -> ChcExpr {
    op(ChcOp::Eq, vec![left, right])
}

#[test]
fn complete_ordered_function_registry_changes_identity_even_when_unused() {
    let rows = || vec![query(ChcExpr::Bool(false), vec![])];
    let functions = vec![
        function("unused", vec![bv(72)], bv(136)),
        function("constant", vec![], bv(1)),
    ];
    let first = source(functions.clone(), rows()).unwrap();
    assert_eq!(first.function_declarations(), functions);
    let mut reversed = functions.clone();
    reversed.reverse();
    assert_ne!(
        first.source_smtlib(),
        source(reversed, rows()).unwrap().source_smtlib()
    );
    let changed = vec![
        function("unused", vec![bv(72)], bv(128)),
        functions[1].clone(),
    ];
    assert_ne!(
        first.source_smtlib(),
        source(changed, rows()).unwrap().source_smtlib()
    );
    assert_ne!(
        first.source_smtlib(),
        source(vec![], rows()).unwrap().source_smtlib()
    );
    let old = QuantifiedChcProblem::new(ChcProblem::new(), rows()).unwrap();
    assert_eq!(
        old.source_smtlib(),
        source(vec![], rows()).unwrap().source_smtlib()
    );
    assert_eq!(first.source_problem().clauses().len(), 1);
    assert_eq!(first.source_problem().pruned_false_query_count(), 0);
}

#[test]
fn function_results_work_in_predicate_arguments_and_complete_grouped_matrices() {
    let mut declarations = ChcProblem::new();
    let predicate = declarations.declare_predicate("P", vec![bv(136)]);
    let functions = vec![
        function("summary", vec![ChcSort::Bool, bv(64)], bv(136)),
        function("seed", vec![], bv(136)),
    ];
    let index = var("i", bv(64));
    let application = call(
        "summary",
        bv(136),
        vec![var("flag", ChcSort::Bool), index.clone()],
    );
    let matrix = op(
        ChcOp::Implies,
        vec![
            op(ChcOp::BvULt, vec![index, var("limit", bv(64))]),
            eq(application.clone(), call("seed", bv(136), vec![])),
        ],
    );
    let rows = vec![
        QuantifiedHornClause::new(
            HornClause::fact(
                ChcExpr::Bool(true),
                predicate,
                vec![call(
                    "summary",
                    bv(136),
                    vec![ChcExpr::Bool(true), ChcExpr::BitVec(0, 64)],
                )],
            ),
            vec![UniversalPremise::with_binders(
                vec![ChcVar::new("i", bv(64)), ChcVar::new("j", bv(64))],
                matrix.clone(),
            )
            .unwrap()],
        ),
        QuantifiedHornClause::new(
            HornClause::query(ClauseBody::predicates_only(vec![(
                predicate,
                vec![call("seed", bv(136), vec![])],
            )])),
            vec![],
        ),
    ];
    let admitted = QuantifiedChcProblem::new_with_functions(declarations, functions, rows).unwrap();
    assert_eq!(admitted.premises()[0][0].matrix(), &matrix);
    let text = admitted.source_smtlib();
    assert!(text.contains("(declare-fun summary (Bool (_ BitVec 64)) (_ BitVec 136))"));
    assert!(text.contains("(forall ((i (_ BitVec 64)) (j (_ BitVec 64)))"));
    assert!(text.contains("(summary flag i)"));
    assert!(text.contains("(P (summary true (_ bv0 64)))"));
    assert!(text.contains("(=> (P seed) false)"));
}

#[test]
fn wrong_arguments_results_and_undeclared_calls_refuse_in_all_source_positions() {
    let functions = || vec![function("f", vec![bv(8)], bv(136))];
    let bad_calls = vec![
        call("f", bv(136), vec![]),
        call("f", bv(136), vec![ChcExpr::BitVec(0, 9)]),
        call("f", bv(128), vec![ChcExpr::BitVec(0, 8)]),
        call("f", ChcSort::Bool, vec![ChcExpr::BitVec(0, 8)]),
        call("missing", bv(136), vec![ChcExpr::BitVec(0, 8)]),
    ];
    for expression in bad_calls {
        let invalid = eq(expression.clone(), expression);
        assert!(source(
            functions(),
            vec![query(
                op(ChcOp::And, vec![ChcExpr::Bool(false), invalid.clone()]),
                vec![]
            )]
        )
        .is_err());
        assert!(source(
            functions(),
            vec![query(
                ChcExpr::Bool(false),
                vec![premise("i", 64, invalid.clone())]
            )]
        )
        .is_err());
        let mut declarations = ChcProblem::new();
        let p = declarations.declare_predicate("P", vec![ChcSort::Bool]);
        for row in [
            HornClause::fact(ChcExpr::Bool(false), p, vec![invalid.clone()]),
            HornClause::query(ClauseBody::predicates_only(vec![(
                p,
                vec![invalid.clone()],
            )])),
        ] {
            assert!(QuantifiedChcProblem::new_with_functions(
                declarations.clone(),
                functions(),
                vec![
                    QuantifiedHornClause::new(row, vec![]),
                    query(ChcExpr::Bool(false), vec![])
                ]
            )
            .is_err());
        }
    }
}

#[test]
fn free_and_unused_bound_names_cannot_capture_ordinary_functions() {
    let functions = || vec![function("f", vec![], bv(8))];
    assert!(source(
        functions(),
        vec![query(eq(var("f", bv(8)), ChcExpr::BitVec(0, 8)), vec![])]
    )
    .is_err());
    assert!(source(
        functions(),
        vec![query(
            ChcExpr::Bool(false),
            vec![premise("f", 8, ChcExpr::Bool(true))]
        )]
    )
    .is_err());
    let matrix = eq(call("f", bv(8), vec![]), ChcExpr::BitVec(0, 8));
    assert!(source(
        functions(),
        vec![query(
            ChcExpr::Bool(false),
            vec![premise("f", 8, matrix.clone())]
        )]
    )
    .is_err());
    assert!(source(
        functions(),
        vec![query(
            ChcExpr::Bool(false),
            vec![premise("index", 8, matrix)]
        )]
    )
    .is_ok());
}

#[test]
fn function_and_source_width_copy_allowances_are_cumulative_not_independent() {
    let wide = bv(crate::MAX_BITVECTOR_WIDTH);
    let functions = || {
        vec![function(
            "wide_signature",
            vec![wide.clone(); 20],
            wide.clone(),
        )]
    };
    let rows = || {
        (0..12)
            .map(|_| {
                query(
                    eq(
                        ChcExpr::BitVec(0, crate::MAX_BITVECTOR_WIDTH),
                        ChcExpr::BitVec(0, crate::MAX_BITVECTOR_WIDTH),
                    ),
                    vec![],
                )
            })
            .collect()
    };
    assert!(source(functions(), vec![query(ChcExpr::Bool(false), vec![])]).is_ok());
    assert!(source(vec![], rows()).is_ok());
    assert!(source(functions(), rows()).is_err());
}

#[test]
fn record_operation_authentication_is_unchanged_beside_declared_functions() {
    let mut declarations = ChcProblem::new();
    declarations.add_datatype_def(
        "R".into(),
        vec![("mkR".into(), vec![("field".into(), bv(8))])],
    );
    let records = super::super::records::Registry::new(&declarations).unwrap();
    let record = records.lookup("R").unwrap().clone();
    let raw = call("mkR", record.clone(), vec![ChcExpr::BitVec(7, 8)]);
    let read = call("field", bv(8), vec![raw]);
    let functions = || vec![function("f", vec![bv(8)], bv(8))];
    let body = eq(call("f", bv(8), vec![read]), ChcExpr::BitVec(7, 8));
    let good = QuantifiedChcProblem::new_with_functions(
        declarations.clone(),
        functions(),
        vec![query(body, vec![])],
    )
    .unwrap();
    assert!(good
        .source_smtlib()
        .contains("(f (field ((as mkR R) (_ bv7 8))))"));
    let wrong = call("field", bv(8), vec![ChcExpr::BitVec(7, 8)]);
    assert!(QuantifiedChcProblem::new_with_functions(
        declarations,
        functions(),
        vec![query(eq(wrong, ChcExpr::BitVec(7, 8)), vec![])]
    )
    .is_err());
}
