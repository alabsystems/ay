// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Ordinary call-summary functions stay global; no real callee is executed.

use super::super::{render, SourceControl};
use super::*;
use std::fmt::Write as _;

mod fixtures;
mod oracle;
use fixtures::{linear, Calls, Cells, Point, Query};

fn output(source: &QuantifiedChcProblem, indices: &[usize]) -> String {
    let token = CancellationToken::new();
    let control = SourceControl::new(Instant::now() + Duration::from_secs(30), &token);
    let edges: Vec<_> = (0..indices.len())
        .map(|i| if i == 0 { vec![] } else { vec![i - 1] })
        .collect();
    render::render_derivation(source, indices, &edges, &control).unwrap()
}

#[test]
fn independent_total_function_tables_distinguish_congruence_and_source_twins() {
    for (calls, cells, query, expected) in [
        (
            Calls::DistinctArgument,
            Cells::Filled,
            Query::DifferentOutputs,
            2,
        ),
        (
            Calls::DistinctSymbol,
            Cells::Filled,
            Query::DifferentOutputs,
            2,
        ),
        (Calls::Congruent, Cells::Filled, Query::DifferentOutputs, 0),
        (
            Calls::DistinctArgument,
            Cells::CorruptLast,
            Query::DifferentOutputs,
            0,
        ),
        (
            Calls::DistinctArgument,
            Cells::Filled,
            Query::ContradictoryInput,
            0,
        ),
    ] {
        let source = linear(calls, cells, query);
        assert_eq!(oracle::model_count(&source, calls, cells), expected);
    }
}

#[test]
fn original_replay_declares_one_global_function_and_reserves_unused_symbols() {
    let source = linear(
        Calls::DistinctArgument,
        Cells::Filled,
        Query::DifferentOutputs,
    );
    assert!(source.source_problem().is_fixedpoint_format());
    assert_eq!(source.function_declarations().len(), 3);
    let replay = output(&source, &[0, 1, 2, 3]);
    for name in ["uf_call_0_pure", "uf_call_1_other", "ay_qcex_0"] {
        assert_eq!(replay.matches(&format!("(declare-fun {name} ")).count(), 1);
    }
    assert_eq!(replay.matches("(uf_call_0_pure ").count(), 2);
    assert!(!replay.contains("(declare-const ay_qcex_0 "));
    assert_eq!(replay.matches("(forall ((").count(), 1);
    assert!(replay.contains("(_ bv65 64)"));
    assert!(!replay.contains("(P "));
    assert!(!replay.contains("(declare-fun P "));
    ay_frontend::parse(&replay).expect("standalone original SMT obligation");
}

#[test]
fn premise_only_function_keeps_both_universal_axes_and_its_declaration() {
    let source = fixtures::grouped(Point::Unconstrained);
    let premise = &source.premises()[0][0];
    assert_eq!(premise.binder_count(), 2);
    assert!(premise
        .binders()
        .all(|binder| binder.sort == ChcSort::BitVec(64)));
    let replay = output(&source, &[0, 1, 2]);
    assert_eq!(replay.matches("(declare-fun uf_range ").count(), 1);
    assert_eq!(replay.matches("(uf_range ").count(), 1);
    let mut binders = String::new();
    for binder in premise.binders() {
        write!(
            &mut binders,
            "({} (_ BitVec 64))",
            ay_core::quote_symbol(&binder.name)
        )
        .unwrap();
    }
    assert!(replay.contains(&format!("(forall ({binders})")));
    assert!(replay.contains("(_ bv34 64)"));
    assert!(replay.contains("(_ bv2 64)"));
    assert!(oracle::grouped_holds(&source, true));
    assert!(!oracle::grouped_holds(&source, false));
    for point in [false, true] {
        assert!(!oracle::grouped_holds(
            &fixtures::grouped(Point::Contradiction),
            point
        ));
    }
}

#[test]
fn a_saved_function_argument_is_not_captured_by_a_later_same_named_binder() {
    let source = fixtures::shadowed();
    let ClauseHead::Predicate(_, args) = &source.source_problem().clauses()[0].head else {
        panic!("head")
    };
    let ChcExpr::Var(outer) = &args[0] else {
        panic!("outer variable")
    };
    let premise = &source.premises()[0][0];
    assert_ne!(outer.name, premise.binder().name);
    let ChcExpr::Op(ChcOp::Implies, matrix) = premise.matrix() else {
        panic!("matrix")
    };
    let ChcExpr::Op(ChcOp::Eq, result) = matrix[1].as_ref() else {
        panic!("result")
    };
    let ChcExpr::FuncApp(name, ChcSort::BitVec(1), arguments) = result[0].as_ref() else {
        panic!("saved call")
    };
    assert_eq!(name, "uf_saved");
    assert_eq!(arguments[0].as_ref(), &ChcExpr::Var(outer.clone()));
    let replay = output(&source, &[0, 1]);
    assert_eq!(replay.matches("(declare-fun uf_saved ").count(), 1);
    assert!(replay.contains(&format!(
        "(uf_saved {})",
        ay_core::quote_symbol(&outer.name)
    )));
}

fn native(calls: Calls) {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(TERM_BUDGET));
    let deadline = Instant::now() + Duration::from_secs(120);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let token = CancellationToken::new();
    let source = linear(calls, Cells::Filled, Query::DifferentOutputs);
    let evidence = require_unsafe(&source, deadline, &token);
    assert_eq!(evidence.clause_indices(), &[0, 1, 2, 3]);
    assert_eq!(
        evidence.premise_steps(),
        &[vec![], vec![0], vec![1], vec![2]]
    );
    assert_eq!(evidence.replay_obligation(), output(&source, &[0, 1, 2, 3]));
    assert!(evidence.recheck(&source, remaining(deadline), &token));
    assert!(Instant::now() < deadline);
    // Complete function definitions now accompany locals from one acquisition.
    let trace = evidence
        .concrete_trace(&source, remaining(deadline), &token)
        .expect("supported scalar UF interpretations and complete local values");
    assert_eq!(trace.function_models().len(), 3);
    for (model, declaration) in trace
        .function_models()
        .iter()
        .zip(source.function_declarations())
    {
        assert_eq!(model.name(), declaration.name());
        assert!(trace
            .replay_obligation()
            .contains(model.definition_smtlib()));
    }
    assert_eq!(trace.replay_obligation().matches("(forall ((").count(), 1);
    assert!(trace.recheck(&source, remaining(deadline), &token));
    let changed = linear(calls, Cells::Filled, Query::ContradictoryInput);
    assert!(!evidence.recheck(&changed, remaining(deadline), &token));
    assert!(evidence.recheck(&source, remaining(deadline), &token));
    assert!(Instant::now() < deadline);
}

#[test]
#[timeout(180000)]
fn distinct_argument_calls_have_a_checked_source_counterexample_and_complete_trace() {
    native(Calls::DistinctArgument);
}

#[test]
#[timeout(180000)]
fn different_global_function_symbols_may_return_different_values_at_the_same_arguments() {
    native(Calls::DistinctSymbol);
}

#[test]
#[timeout(180000)]
fn congruence_false_full_premise_and_false_query_never_acquire_either_authority() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(TERM_BUDGET));
    let deadline = Instant::now() + Duration::from_secs(120);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    for (calls, cells, query) in [
        (Calls::Congruent, Cells::Filled, Query::DifferentOutputs),
        (
            Calls::DistinctArgument,
            Cells::CorruptLast,
            Query::DifferentOutputs,
        ),
        (
            Calls::DistinctArgument,
            Cells::Filled,
            Query::ContradictoryInput,
        ),
    ] {
        let source = linear(calls, cells, query);
        assert!(Instant::now() < deadline);
        assert!(matches!(
            source.solve(
                remaining(deadline).min(Duration::from_secs(30)),
                Some(TERM_BUDGET),
                &CancellationToken::new()
            ),
            QuantifiedChcResult::Unknown
        ));
    }
}

#[test]
#[timeout(180000)]
fn a_joint_premise_only_function_uses_full_native_source_validation() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(TERM_BUDGET));
    let deadline = Instant::now() + Duration::from_secs(120);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let token = CancellationToken::new();
    let source = fixtures::grouped(Point::Unconstrained);
    let evidence = require_unsafe(&source, deadline, &token);
    assert_eq!(evidence.clause_indices(), &[0, 1, 2]);
    assert_eq!(evidence.replay_obligation(), output(&source, &[0, 1, 2]));
    assert!(evidence.recheck(&source, remaining(deadline), &token));
    let trace = evidence
        .concrete_trace(&source, remaining(deadline), &token)
        .expect("complete matrix-only scalar UF interpretation");
    assert_eq!(trace.function_models().len(), 1);
    assert_eq!(trace.function_models()[0].name(), "uf_range");
    assert_eq!(trace.replay_obligation().matches("(forall ((").count(), 1);
    assert!(trace.recheck(&source, remaining(deadline), &token));
    let conflict = fixtures::grouped(Point::Contradiction);
    assert!(!evidence.recheck(&conflict, remaining(deadline), &token));
    assert!(Instant::now() < deadline);
    assert!(matches!(
        conflict.solve(
            remaining(deadline).min(Duration::from_secs(30)),
            Some(TERM_BUDGET),
            &token
        ),
        QuantifiedChcResult::Unknown
    ));
}
