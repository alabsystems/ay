// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::quantified::QuantifiedChcResult;
use ntest::timeout;

#[test]
fn complete_lexical_environment_elaborates_one_shared_lambda_term() {
    let token = CancellationToken::new();
    let source = data_source();
    let rendered = render(&source, &token);
    let registry = registry(&source, &control(&token)).unwrap();
    let text = pins::render(
        &rendered,
        &bindings(&rendered, &range()),
        &[],
        &source,
        &registry,
        &control(&token),
    )
    .unwrap();
    let mut context = ay_frontend::Context::new();
    for command in ay_frontend::parse(&text).unwrap() {
        context.process_command(&command).unwrap();
    }
    assert_eq!(context.assertions.len(), 1);
    let lambdas = (0..context.terms.len()).filter(|index| {
        matches!(context.terms.get(ay_core::TermId(*index as u32)), ay_core::TermData::App(symbol, _)
            if symbol.name() == "lambda-array")
    }).count();
    assert_eq!(lambdas, 1);
}

#[test]
#[timeout(30000)]
fn complete_scalar_trace_retains_unused_functions_and_rejects_changed_full_source() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(128 * 1024 * 1024));
    let end = Instant::now() + Duration::from_secs(20);
    let _deadline = ScopedSmtDeadline::install_until(end);
    let token = CancellationToken::new();
    let input = "(set-logic HORN)
        (declare-fun unused ((_ BitVec 2)) (_ BitVec 2))
        (declare-fun P ((_ BitVec 2)) Bool)
        (assert (forall ((x (_ BitVec 2)))
          (=> (and (= x (_ bv1 2)) (forall ((i (_ BitVec 2))) (= x x))) (P x))))
        (assert (forall ((x (_ BitVec 2))) (=> (and (P x) (= x (_ bv1 2))) false)))
        (check-sat)";
    let source = QuantifiedChcProblem::parse_smtlib(input).unwrap();
    let QuantifiedChcResult::Unsafe(base) = source.solve(
        end.saturating_duration_since(Instant::now()),
        Some(128 * 1024 * 1024),
        &token,
    ) else {
        panic!("full original native Unsafe required");
    };
    let trace = base
        .complete_trace(
            &source,
            end.saturating_duration_since(Instant::now()),
            &token,
        )
        .unwrap();
    assert_eq!(trace.source_smtlib(), source.source_smtlib());
    assert_eq!(trace.function_models().len(), 1);
    assert_eq!(trace.function_models()[0].name(), "unused");
    assert_eq!(trace.replay_obligation().matches("(assert ").count(), 1);
    assert!(trace.replay_obligation().contains("(forall (("));
    assert!(trace.bindings().iter().all(|binding| matches!(
        binding.value(),
        QuantifiedChcCompleteValue::Literal(SmtValue::BitVec(1, 2))
    )));
    assert!(trace.recheck(
        &source,
        end.saturating_duration_since(Instant::now()),
        &token
    ));
    let changed =
        QuantifiedChcProblem::parse_smtlib(&input.replace("unused", "other_unused")).unwrap();
    assert!(!trace.recheck(
        &changed,
        end.saturating_duration_since(Instant::now()),
        &token
    ));
}

#[test]
#[timeout(30000)]
fn complete_array_data_still_requires_fresh_native_check_of_original_pinned_conjunction() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(128 * 1024 * 1024));
    let end = Instant::now() + Duration::from_secs(20);
    let _deadline = ScopedSmtDeadline::install_until(end);
    let token = CancellationToken::new();
    let source = data_source();
    let rendered = render(&source, &token);
    let registry = registry(&source, &control(&token)).unwrap();
    let bindings = bindings(&rendered, &range());
    let owner = SourceControl::new(end, &token);
    let pinned = pins::render(&rendered, &bindings, &[], &source, &registry, &owner).unwrap();
    assert!(replay::validate(
        &pinned,
        end,
        Some(128 * 1024 * 1024),
        &token,
        &owner
    ));
    let corrupted = pinned.replace("(and true", "(and false");
    assert_ne!(corrupted, pinned);
    assert!(!replay::validate(
        &corrupted,
        end,
        Some(128 * 1024 * 1024),
        &token,
        &owner
    ));
}
