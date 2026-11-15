// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Solver-free completion data and output tests; no native SAT seal is forged.

use super::*;
use ay_core::Symbol;
use ay_model_check::{GateVerdict, ModelView};
use num_bigint::BigInt;

mod fixtures;
mod nested_arrays;
mod ownership;

#[test]
fn whole_arrays_fresh_nested_reads_and_both_output_commands_share_the_completion() {
    let (mut executor, model, array) = fixtures::completed();
    let fresh = fixtures::length(&mut executor, array, 9);
    fixtures::assert_five(
        executor
            .completed_model_value(&model, fresh)
            .unwrap()
            .unwrap(),
    );
    assert_eq!(executor.evaluate_term(&model, fresh), fixtures::five());
    let whole = executor
        .completed_model_value(&model, array)
        .unwrap()
        .unwrap();
    assert!(matches!(whole, ModelValue::Array(_)));
    assert!(matches!(
        executor.evaluate_term(&model, array),
        EvalValue::Unknown
    ));

    // Merely install DATA in the private output slot to exercise rendering.
    // Production publication must independently replay the complete roots.
    executor.last_result = Some(crate::executor_types::SolveResult::Sat);
    executor.last_model = Some(model);
    let output = executor.values(&[("a".into(), array), ("fresh_len".into(), fresh)]);
    assert!(!output.starts_with("(error"), "{output}");
    assert!(
        output.contains("(fresh_len #x0000000000000005)"),
        "{output}"
    );
    let printed = executor.model();
    assert!(!printed.starts_with("(error"), "{printed}");
    let literal = executor
        .term_value_string(executor.last_model.as_ref().unwrap(), array)
        .unwrap();
    assert!(output.contains(&format!("(a {literal})")));
    assert!(printed.contains(&literal));
    // An independent exact decoder checks the actual whole-array output,
    // including its default, nested record and complete inner-array value.
    fixtures::check_array_literal(&literal);
}

#[test]
fn old_select_pins_and_result_memos_cannot_replace_the_completed_value() {
    let (mut executor, mut model, array) = fixtures::completed();
    let fresh = fixtures::length(&mut executor, array, 9);
    model.dt_pins.insert(
        fresh,
        EvalValue::BitVec {
            value: 99.into(),
            width: 64,
        },
    );
    let _memo = super::super::EvalMemoSession::new();
    super::super::seed_eval_memo_for_test(
        fresh,
        EvalValue::BitVec {
            value: 88.into(),
            width: 64,
        },
    );
    assert_eq!(executor.evaluate_term(&model, fresh), fixtures::five());
    assert_eq!(
        executor.term_value_string(&model, fresh).unwrap(),
        "#x0000000000000005"
    );
}

#[test]
fn a_defined_array_without_a_direct_member_entry_uses_the_same_base_completion() {
    let (mut executor, assignments, array) = fixtures::assignments();
    let sort = executor.ctx.terms.sort(array).clone();
    let alias = executor.ctx.terms.mk_var("defined_array", sort.clone());
    let key = executor.ctx.terms.mk_bitvec(10.into(), 64);
    let cell_sort = sort.array_element().unwrap().clone();
    let old = executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), [array, key], cell_sort);
    let stored = executor.ctx.terms.mk_store(array, key, old);
    let equation = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), [alias, stored], Sort::Bool);
    executor.ctx.assertions.push(equation);
    let mut model = Model::empty();
    model
        .install_residual_arrays(&executor.ctx, assignments)
        .unwrap();
    assert!(model
        .residual_array_value(&executor.ctx, alias)
        .unwrap()
        .is_none());
    let length = fixtures::length(&mut executor, alias, 9);
    fixtures::assert_five(
        executor
            .completed_model_value(&model, length)
            .unwrap()
            .unwrap(),
    );
    assert_eq!(executor.evaluate_term(&model, length), fixtures::five());
    assert!(!executor
        .term_value_string(&model, alias)
        .unwrap()
        .contains("value-unavailable"));
}

#[test]
fn stale_context_refuses_even_an_unrelated_scalar_without_old_model_fallback() {
    let (mut executor, model, array) = fixtures::completed();
    for command in ay_frontend::parse("(declare-const changed Bool)").unwrap() {
        executor.ctx.process_command(&command).unwrap();
    }
    let literal = executor.ctx.terms.mk_bitvec(7.into(), 64);
    assert!(!model.residual_arrays_are_current(&executor.ctx));
    assert!(executor.completed_model_value(&model, literal).is_err());
    assert!(matches!(
        executor.evaluate_term(&model, literal),
        EvalValue::Unknown
    ));
    assert!(executor.term_value_string(&model, literal).is_err());
    executor.last_model = Some(model);
    executor.last_result = Some(crate::executor_types::SolveResult::Sat);
    assert!(executor
        .values(&[("a".into(), array)])
        .starts_with("(error"));
    assert!(executor.model().starts_with("(error"));
}

#[test]
fn query_census_is_bounded_including_duplicate_edges_and_late_dependencies() {
    let (mut executor, model, array) = fixtures::completed();
    let literal = executor.ctx.terms.mk_bitvec(0.into(), 64);
    let exact = executor.ctx.terms.mk_app(
        Symbol::named("census_only"),
        vec![literal; MAX_QUERY_EDGES - 1],
        Sort::Bool,
    );
    assert!(!executor.depends_on_residual_array(&model, exact).unwrap());
    let mut args = vec![literal; MAX_QUERY_EDGES - 1];
    args.push(array);
    let over = executor
        .ctx
        .terms
        .mk_app(Symbol::named("census_only"), args, Sort::Bool);
    assert!(executor.completed_model_value(&model, over).is_err());
    let fresh = fixtures::length(&mut executor, array, 9);
    fixtures::assert_five(
        executor
            .completed_model_value(&model, fresh)
            .unwrap()
            .unwrap(),
    );
}

#[test]
fn callback_guard_is_scoped_and_unwinding_restores_typed_reads() {
    let (mut executor, model, array) = fixtures::completed();
    let fresh = fixtures::length(&mut executor, array, 9);
    {
        let _scope = EvaluationScope::enter();
        assert!(executor
            .completed_model_value(&model, fresh)
            .unwrap()
            .is_none());
    }
    assert!(std::panic::catch_unwind(|| {
        let _scope = EvaluationScope::enter();
        panic!("authored callback unwind");
    })
    .is_err());
    fixtures::assert_five(
        executor
            .completed_model_value(&model, fresh)
            .unwrap()
            .unwrap(),
    );
}

#[test]
fn scalar_conversion_is_exact_and_never_turns_a_record_into_an_element_token() {
    let executor = Executor::new();
    let five = ModelValue::BitVec {
        value: BigInt::from(5),
        width: 64,
    };
    assert_eq!(
        executor.completed_scalar_value(&five, &Sort::bitvec(64)),
        fixtures::five()
    );
    assert!(matches!(
        executor.completed_scalar_value(&five, &Sort::bitvec(8)),
        EvalValue::Unknown
    ));
    let record = ModelValue::Datatype {
        ctor: "mkInner".into(),
        args: vec![five],
    };
    assert!(matches!(
        executor.completed_scalar_value(&record, &Sort::Uninterpreted("Inner".into())),
        EvalValue::Unknown
    ));
    let literal = executor.ctx.terms.true_term();
    assert!(executor
        .completed_model_value(&Model::empty(), literal)
        .unwrap()
        .is_none());
}

#[test]
fn the_dependency_census_is_memoized_per_session_without_changing_any_answer() {
    use crate::executor::model::eval_memo;
    use crate::executor::model::EvalMemoSession;

    let (mut executor, model, array) = fixtures::completed();
    let literal = executor.ctx.terms.mk_bitvec(0.into(), 64);
    let free =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("census_only"), vec![literal; 8], Sort::Bool);
    let touching = executor
        .ctx
        .terms
        .mk_app(Symbol::named("census_only"), vec![array], Sort::Bool);

    // Outside a session nothing is cached, and the answers are the truth the
    // rest of this file already pins.
    assert!(!executor.depends_on_residual_array(&model, free).unwrap());
    assert!(executor
        .depends_on_residual_array(&model, touching)
        .unwrap());
    assert_eq!(eval_memo::residual_dep_get(free), None);
    assert_eq!(eval_memo::residual_dep_get(touching), None);

    {
        let _session = EvalMemoSession::new();
        assert!(!executor.depends_on_residual_array(&model, free).unwrap());
        // A completed negative walk decides every node it visited, not just
        // the root: that is what makes the enclosing evaluation linear.
        assert_eq!(eval_memo::residual_dep_get(free), Some(false));
        assert_eq!(eval_memo::residual_dep_get(literal), Some(false));

        // An early positive decides the root alone; the nodes it never had to
        // settle must stay unrecorded rather than be guessed.
        assert!(executor
            .depends_on_residual_array(&model, touching)
            .unwrap());
        assert_eq!(eval_memo::residual_dep_get(touching), Some(true));

        // Repeats agree with the uncached walk.
        assert!(!executor.depends_on_residual_array(&model, free).unwrap());
        assert!(executor
            .depends_on_residual_array(&model, touching)
            .unwrap());

        // Every clear point the evaluated values use also drops these answers,
        // so a dependency verdict can never outlive the batch that decided it.
        eval_memo::clear();
        assert_eq!(eval_memo::residual_dep_get(free), None);
        assert_eq!(eval_memo::residual_dep_get(touching), None);
    }
    assert_eq!(eval_memo::residual_dep_get(free), None);
}

#[test]
fn a_walk_that_fails_closed_records_nothing_for_a_later_session_to_trust() {
    use crate::executor::model::eval_memo;
    use crate::executor::model::EvalMemoSession;

    let (mut executor, model, array) = fixtures::completed();
    let literal = executor.ctx.terms.mk_bitvec(0.into(), 64);
    let mut args = vec![literal; MAX_QUERY_EDGES - 1];
    args.push(array);
    let over = executor
        .ctx
        .terms
        .mk_app(Symbol::named("census_only"), args, Sort::Bool);

    let _session = EvalMemoSession::new();
    assert!(executor.depends_on_residual_array(&model, over).is_err());
    assert_eq!(eval_memo::residual_dep_get(over), None);
    assert_eq!(eval_memo::residual_dep_get(literal), None);
}
