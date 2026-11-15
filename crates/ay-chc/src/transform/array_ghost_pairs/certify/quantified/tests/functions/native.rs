// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::quantified::QuantifiedChcResult;
use crate::smt::ScopedSmtDeadline;
use ntest::timeout;

const TERM_BUDGET: usize = 128 * 1024 * 1024;

fn public_safe(shape: Shape) {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(TERM_BUDGET));
    let end = Instant::now() + Duration::from_secs(120);
    let _deadline = ScopedSmtDeadline::install_until(end);
    let source = fixtures::source(shape, Calls::Same, Query::Same);
    let token = CancellationToken::new();
    let QuantifiedChcResult::Safe(evidence) =
        source.solve(Duration::from_secs(80), Some(TERM_BUDGET), &token)
    else {
        panic!("the shared global UF and complete array premise must synthesize Safe");
    };
    assert_eq!(evidence.source_smtlib(), source.source_smtlib());
    assert_eq!(evidence.replay_obligations().len(), 3);
    for (index, obligation) in evidence.replay_obligations().iter().enumerate() {
        assert_eq!(obligation.clause_index, index);
        complete_declarations(&source, &obligation.smtlib);
    }
    full_premise(&source, &evidence.replay_obligations()[0].smtlib);
    assert!(evidence.recheck(
        &source,
        end.saturating_duration_since(Instant::now()),
        &token
    ));
    let wrong = fixtures::source(shape, Calls::Independent, Query::Same);
    assert!(!evidence.recheck(
        &wrong,
        end.saturating_duration_since(Instant::now()),
        &token
    ));
    assert!(Instant::now() < end);
}

#[test]
#[timeout(180000)]
fn scalar_array_global_function_fill_synthesizes_and_rechecks_safe() {
    public_safe(Shape::Array);
}

#[test]
#[timeout(180000)]
fn full_vec_global_function_fill_synthesizes_and_rechecks_original_safe() {
    public_safe(Shape::Vec);
}

#[test]
#[timeout(180000)]
fn nested_vec_global_function_fill_synthesizes_independent_row_column_safe() {
    public_safe(Shape::Nested);
}

#[test]
#[timeout(180000)]
fn independent_functions_and_shifted_query_cannot_certify_the_wrong_array_property() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(TERM_BUDGET));
    let end = Instant::now() + Duration::from_secs(120);
    let _deadline = ScopedSmtDeadline::install_until(end);
    let cases = [
        (Shape::Vec, Calls::Independent, Query::Same),
        (Shape::Nested, Calls::Independent, Query::Same),
        (Shape::Nested, Calls::Same, Query::Shifted),
    ];
    for (index, (shape, calls, query)) in cases.into_iter().enumerate() {
        let source = fixtures::source(shape, calls, query);
        assert!(
            oracle::bad_state(&source, shape, calls),
            "genuine reachable wrong state"
        );
        let remaining = end.saturating_duration_since(Instant::now());
        assert!(!remaining.is_zero(), "each negative gets a live invocation");
        assert!(!matches!(
            source.solve(
                remaining / u32::try_from(cases.len() - index).unwrap(),
                Some(TERM_BUDGET),
                &CancellationToken::new(),
            ),
            QuantifiedChcResult::Safe(_)
        ));
    }
}
