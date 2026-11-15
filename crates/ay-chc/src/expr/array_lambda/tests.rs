// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::smt::{SmtContext, SmtResult, SmtValue};
use ay_core::kani_compat::DetHashMap;

fn variable(name: &str) -> ChcVar {
    ChcVar::new(name, ChcSort::Int)
}
fn captured() -> ChcExpr {
    let i = variable("i");
    ChcExpr::array_lambda(
        i.clone(),
        ChcExpr::add(ChcExpr::Var(i), ChcExpr::Var(variable("x"))),
    )
    .expect("well-typed lambda")
}
fn read(array: ChcExpr, index: ChcExpr) -> ChcExpr {
    ChcExpr::Op(crate::ChcOp::Select, vec![Arc::new(array), Arc::new(index)])
}
fn value(array: ChcExpr, index: i128, model: &DetHashMap<String, SmtValue>) -> Option<SmtValue> {
    crate::expr::evaluate_expr(&read(array, ChcExpr::Int(index)), model)
}

#[test]
fn free_capture_substitution_reaches_environment() {
    let expression = captured().substitute(&[(variable("x"), ChcExpr::Int(7))]);
    assert!(expression.vars().is_empty());
    assert_eq!(
        value(expression, 3, &DetHashMap::default()),
        Some(SmtValue::Int(10))
    );
}

#[test]
fn inserting_original_binder_name_does_not_capture_it() {
    let expression = captured().substitute(&[(variable("x"), ChcExpr::Var(variable("i")))]);
    assert_eq!(expression.vars(), vec![variable("i")]);
    let model = [("i".into(), SmtValue::Int(8))].into_iter().collect();
    assert_eq!(value(expression, 3, &model), Some(SmtValue::Int(11)));
}

#[test]
fn parallel_capture_substitution_does_not_substitute_inserted_values() {
    let i = variable("i");
    let expression = ChcExpr::array_lambda(
        i,
        ChcExpr::sub(ChcExpr::Var(variable("x")), ChcExpr::Var(variable("y"))),
    )
    .expect("typed body")
    .substitute(&[
        (variable("x"), ChcExpr::Var(variable("y"))),
        (variable("y"), ChcExpr::Int(2)),
    ]);
    let model = [("y".into(), SmtValue::Int(9))].into_iter().collect();
    assert_eq!(value(expression, 0, &model), Some(SmtValue::Int(7)));
}

#[test]
fn sort_changing_capture_substitution_is_rejected_by_converter() {
    let expression = captured().substitute(&[(variable("x"), ChcExpr::Bool(true))]);
    let mut context = SmtContext::new();
    context.convert_expr(&expression);
    assert!(context.conversion_budget_exceeded());
}

#[test]
fn malformed_matrix_is_rejected_before_closing() {
    let bad = ChcExpr::Op(
        crate::ChcOp::Add,
        vec![Arc::new(ChcExpr::Bool(true)), Arc::new(ChcExpr::Int(1))],
    );
    assert!(ChcExpr::array_lambda(variable("i"), bad).is_err());
    assert!(ChcExpr::array_lambda(ChcVar::new("i", ChcSort::BitVec(0)), ChcExpr::Int(1)).is_err());
}

#[test]
fn core_conversion_keeps_two_capture_environments_distinct() {
    let original = captured();
    let a = original.substitute(&[(variable("x"), ChcExpr::Int(7))]);
    let b = original.substitute(&[(variable("x"), ChcExpr::Int(9))]);
    let query = ChcExpr::eq(read(a, ChcExpr::Int(4)), read(b, ChcExpr::Int(2)));
    let mut context = SmtContext::new();
    assert!(matches!(
        context.check_sat(&ChcExpr::not(query)),
        SmtResult::Unsat
    ));
}

#[test]
fn solver_preserves_symbolic_index_and_capture_relation() {
    let query = ChcExpr::and(
        ChcExpr::eq(ChcExpr::Var(variable("x")), ChcExpr::Int(7)),
        ChcExpr::ne(
            read(captured(), ChcExpr::Var(variable("j"))),
            ChcExpr::add(ChcExpr::Var(variable("j")), ChcExpr::Int(7)),
        ),
    );
    let mut context = SmtContext::new();
    assert!(matches!(context.check_sat(&query), SmtResult::Unsat));
}

#[test]
fn solver_does_not_treat_lambda_as_uninterpreted_array() {
    let query = ChcExpr::eq(read(captured(), ChcExpr::Int(4)), ChcExpr::Int(20));
    let mut context = SmtContext::new();
    assert!(matches!(context.check_sat(&query), SmtResult::Sat(_)));
}

#[test]
fn structural_identity_covers_template_and_captures() {
    use std::hash::{Hash, Hasher};
    fn hash(value: &ChcExpr) -> u64 {
        let mut h = std::collections::hash_map::DefaultHasher::new();
        value.hash(&mut h);
        h.finish()
    }
    let a = captured();
    let b = a.substitute(&[(variable("x"), ChcExpr::Int(3))]);
    let c = ChcExpr::array_lambda(variable("i"), ChcExpr::Int(3)).expect("closed");
    assert_ne!(a, b);
    assert_ne!(b, c);
    assert_ne!(hash(&a), hash(&b));
    assert_ne!(hash(&b), hash(&c));
    assert_eq!(hash(&a), hash(&a.clone()));
}

#[test]
fn core_lambda_is_not_reexported_as_an_uninterpreted_function() {
    let mut context = SmtContext::new();
    let term = context.convert_expr(&captured());
    assert!(context.term_to_chc_expr(term).is_none());
}

#[test]
fn bounded_template_rejects_exponential_tree_expansion() {
    let mut body = Arc::new(ChcExpr::Var(variable("i")));
    for _ in 0..17 {
        body = Arc::new(ChcExpr::Op(crate::ChcOp::Add, vec![body.clone(), body]));
    }
    assert!(ChcExpr::array_lambda(variable("i"), (*body).clone()).is_err());
}

#[test]
fn lambda_binder_sort_is_bounded_before_cloning() {
    let mut sort = ChcSort::Int;
    for _ in 0..260 {
        sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(sort));
    }
    assert!(ChcExpr::array_lambda(ChcVar::new("i", sort), ChcExpr::Int(0)).is_err());
}

#[test]
fn rewritten_capture_function_cannot_shadow_fresh_core_binder() {
    let call = ChcExpr::FuncApp("ay!lambda!index_0".into(), ChcSort::Int, vec![]);
    let expression = captured().substitute(&[(variable("x"), call)]);
    let ChcExpr::ArrayLambda(lambda) = &expression else {
        panic!("lambda");
    };
    assert_eq!(
        lambda.conversion_prefix().expect("complete symbol census"),
        "ay!lambda!index!"
    );
}

#[test]
fn enclosing_dag_let_cannot_capture_template_function() {
    use crate::smt::dag_smtlib::{write_asserts_dag, DagCaps};
    let i = variable("i");
    let function = ChcExpr::FuncApp(
        "_d0".into(),
        ChcSort::Int,
        vec![Arc::new(ChcExpr::Var(i.clone()))],
    );
    let lambda = ChcExpr::array_lambda(i, function).expect("typed UF lambda");
    let shared = Arc::new(ChcExpr::add(ChcExpr::Var(variable("x")), ChcExpr::Int(1)));
    let left = ChcExpr::Op(
        crate::ChcOp::Eq,
        vec![shared.clone(), Arc::new(ChcExpr::Int(2))],
    );
    let right = ChcExpr::Op(
        crate::ChcOp::Eq,
        vec![shared, Arc::new(read(lambda, ChcExpr::Int(3)))],
    );
    let expression = ChcExpr::and(left, right);
    let mut text = String::new();
    write_asserts_dag(
        &mut text,
        &[&expression],
        DagCaps {
            max_unique_nodes: 1000,
            max_depth: 100,
        },
    )
    .expect("bounded DAG");
    assert!(text.contains("(_d0 "), "{text}");
    assert!(text.contains("(_d_0 "), "{text}");
    assert!(!text.contains("(let ((_d0 "), "{text}");
}

#[test]
fn array_lambda_selection_through_store_preserves_written_and_unwritten_indices() {
    let array = captured().substitute(&[(variable("x"), ChcExpr::Int(7))]);
    let stored = ChcExpr::store(array, ChcExpr::Int(3), ChcExpr::Int(99));
    assert_eq!(
        value(stored.clone(), 3, &DetHashMap::default()),
        Some(SmtValue::Int(99))
    );
    assert_eq!(
        value(stored, 4, &DetHashMap::default()),
        Some(SmtValue::Int(11))
    );
}

#[test]
fn array_lambda_selection_through_ite_uses_only_the_selected_branch() {
    let a = captured().substitute(&[(variable("x"), ChcExpr::Int(7))]);
    let b = captured().substitute(&[(variable("x"), ChcExpr::Int(20))]);
    let condition = ChcVar::new("condition", ChcSort::Bool);
    let array = ChcExpr::ite(ChcExpr::Var(condition), a, b);
    let yes = [("condition".into(), SmtValue::Bool(true))]
        .into_iter()
        .collect();
    let no = [("condition".into(), SmtValue::Bool(false))]
        .into_iter()
        .collect();
    assert_eq!(value(array.clone(), 3, &yes), Some(SmtValue::Int(10)));
    assert_eq!(value(array.clone(), 3, &no), Some(SmtValue::Int(23)));
    assert_eq!(value(array, 3, &DetHashMap::default()), None);
}

#[test]
fn array_lambda_selection_never_guesses_an_unassigned_store_index() {
    let array = captured().substitute(&[(variable("x"), ChcExpr::Int(7))]);
    let stored = ChcExpr::store(array, ChcExpr::Var(variable("unknown")), ChcExpr::Int(99));
    assert_eq!(value(stored, 3, &DetHashMap::default()), None);
}

fn lambda_resource_query() -> ChcExpr {
    let index = variable("resource_index");
    let mut body = ChcExpr::Var(index.clone());
    for n in 0..8 {
        body = ChcExpr::Op(
            crate::ChcOp::Add,
            vec![Arc::new(body), Arc::new(ChcExpr::Int(n))],
        );
    }
    let lambda = Arc::new(ChcExpr::array_lambda(index, body).expect("closed typed code"));
    ChcExpr::Op(crate::ChcOp::Eq, vec![lambda.clone(), lambda])
}

#[test]
fn lambda_dag_node_caps_include_closed_code() {
    use crate::smt::dag_smtlib::{count_dag, write_asserts_dag, DagCaps, DagError};
    let query = lambda_resource_query();
    let caps = DagCaps {
        max_unique_nodes: 2,
        max_depth: 100,
    };
    assert!(matches!(
        count_dag(&[&query], caps),
        Err(DagError::UniqueNodeCap)
    ));
    let mut text = String::from("unchanged");
    assert!(matches!(
        write_asserts_dag(&mut text, &[&query], caps),
        Err(DagError::UniqueNodeCap)
    ));
    assert_eq!(text, "unchanged");
}

#[test]
fn lambda_dag_depth_caps_include_closed_code() {
    use crate::smt::dag_smtlib::{count_dag, write_asserts_dag, DagCaps, DagError};
    let query = lambda_resource_query();
    let caps = DagCaps {
        max_unique_nodes: 100,
        max_depth: 1,
    };
    assert!(matches!(
        count_dag(&[&query], caps),
        Err(DagError::DepthCap)
    ));
    let mut text = String::from("unchanged");
    assert!(matches!(
        write_asserts_dag(&mut text, &[&query], caps),
        Err(DagError::DepthCap)
    ));
    assert_eq!(text, "unchanged");
}

#[test]
fn lambda_dag_counts_closed_code_under_adequate_caps() {
    use crate::smt::dag_smtlib::{count_dag, write_asserts_dag, DagCaps};
    let query = lambda_resource_query();
    let caps = DagCaps {
        max_unique_nodes: 100,
        max_depth: 100,
    };
    let stats = count_dag(&[&query], caps).expect("sufficient semantic budget");
    assert_eq!(stats.unique_nodes, 19);
    assert_eq!(stats.max_depth, 10);
    let mut text = String::new();
    let written =
        write_asserts_dag(&mut text, &[&query], caps).expect("sufficient semantic budget");
    assert_eq!(written, stats);
    assert!(
        text.contains("(lambda (("),
        "closed lambda remains in emitted formula: {text}"
    );
}

#[test]
fn array_lambda_depth_miss_is_not_reused_at_a_shallower_call() {
    use crate::expr::dag::eval_memo::{memo_active, with_memo_disabled, EvalScope};
    let index = variable("depth_index");
    let mut body = ChcExpr::Var(index.clone());
    for _ in 0..240 {
        body = ChcExpr::Op(
            crate::ChcOp::Add,
            vec![Arc::new(body), Arc::new(ChcExpr::Int(1))],
        );
    }
    let lambda = ChcExpr::array_lambda(index, body).expect("bounded deep matrix");
    let selected = Arc::new(read(lambda, ChcExpr::Int(0)));
    let mut shared = Arc::new(ChcExpr::Bool(true));
    for _ in 0..16 {
        shared = Arc::new(ChcExpr::Op(crate::ChcOp::And, vec![shared.clone(), shared]));
    }
    let model = DetHashMap::default();
    let mut saw_deep_miss = false;
    for depth in [40, 80, 120, 160, 200, 240, 280, 320, 360, 400] {
        let mut deep = selected.clone();
        for _ in 0..depth {
            deep = Arc::new(ChcExpr::Op(
                crate::ChcOp::Add,
                vec![deep, Arc::new(ChcExpr::Int(0))],
            ));
        }
        let expected = with_memo_disabled(|| {
            (
                crate::expr::evaluate_expr(&deep, &model),
                crate::expr::evaluate_expr(&selected, &model),
            )
        });
        assert_eq!(expected.1, Some(SmtValue::Int(240)));
        saw_deep_miss |= expected.0.is_none();
        let actual = {
            let _scope =
                EvalScope::enter([deep.as_ref(), selected.as_ref(), shared.as_ref()], &model);
            assert!(memo_active(), "shared roots must activate the memo");
            let deep_result = crate::expr::evaluate_expr(&deep, &model);
            assert_eq!(crate::Mbp::new().eval_bool(&selected, &model), None);
            (deep_result, crate::expr::evaluate_expr(&selected, &model))
        };
        assert_eq!(
            actual, expected,
            "depth={depth}: a deep miss cannot poison the shallow result"
        );
    }
    assert!(
        saw_deep_miss,
        "control must exercise the existing depth refusal"
    );
}

#[test]
fn array_lambda_scalar_reads_reject_opaque_model_values() {
    let index = variable("typed_index");
    let identity =
        ChcExpr::array_lambda(index.clone(), ChcExpr::Var(index.clone())).expect("typed identity");
    let constant = ChcExpr::array_lambda(index.clone(), ChcExpr::Int(42)).expect("typed constant");
    let captured =
        ChcExpr::array_lambda(index, ChcExpr::Var(variable("typed_value"))).expect("typed capture");
    let wrong = SmtValue::Opaque("not-an-integer".into());
    let model: DetHashMap<String, SmtValue> = [
        ("typed_index".into(), wrong.clone()),
        ("typed_value".into(), wrong),
    ]
    .into_iter()
    .collect();
    for array in [identity, constant] {
        let expression = read(array, ChcExpr::Var(variable("typed_index")));
        assert_eq!(
            crate::expr::evaluate_expr(&expression, &model),
            None,
            "an Int index needs an integer model value"
        );
    }
    assert_eq!(
        value(captured, 0, &model),
        None,
        "an Int element needs an integer model value"
    );
}

#[test]
fn array_lambda_composite_results_remain_valid() {
    let lambda = ChcExpr::array_lambda(
        variable("index"),
        ChcExpr::const_array(ChcSort::Int, ChcExpr::Int(7)),
    )
    .unwrap();
    assert_eq!(
        value(lambda, 0, &DetHashMap::default()),
        Some(SmtValue::ConstArray(Box::new(SmtValue::Int(7))))
    );
}
