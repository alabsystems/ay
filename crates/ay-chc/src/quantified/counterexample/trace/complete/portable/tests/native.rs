// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Runtime-intended native controls; private wire/prepared DATA is not a pass.

use super::*;
use crate::quantified::QuantifiedChcCompleteResult;
use ntest::timeout;

fn remaining(end: Instant) -> Duration {
    end.saturating_duration_since(Instant::now())
}

#[test]
#[timeout(30000)]
fn whole_range_artifact_roundtrip_requires_native_pins_with_one_twenty_second_end() {
    let end = Instant::now() + WALL;
    let _wall = ScopedSmtDeadline::install_until(end);
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(MEMORY));
    let token = CancellationToken::new();
    let problem = source();
    // An unsealed fixture cannot escape through either public boundary unless
    // its complete original-source conjunction actually receives checked SAT.
    let trace = unchecked(&problem, &range(), &token);
    let bytes = trace
        .export_artifact(&problem, remaining(end), &token)
        .unwrap();
    let imported = problem
        .validate_complete_trace_artifact(&bytes, remaining(end), Some(MEMORY), &token)
        .unwrap();
    assert_eq!(
        imported.trace().replay_obligation(),
        trace.replay_obligation()
    );
    assert_eq!(imported.trace().source_smtlib(), problem.source_smtlib());
    assert_eq!(
        imported.artifact_sha256(),
        codec_transport::digest(&bytes, &control(&token)).unwrap()
    );
    let QuantifiedChcCompleteValue::FunctionalArray(array) = imported.trace().bindings()[0].value()
    else {
        panic!("full array, not sampled cells");
    };
    assert_scalar_eq(&read(array, (1 << 40) - 1), &bv(9, 8));
    assert_scalar_eq(&read(array, 1 << 40), &bv(0, 8));
    assert!(Instant::now() < end);
}

#[test]
#[timeout(30000)]
fn wrong_saved_range_with_recomputed_digest_cannot_choose_a_different_model() {
    let end = Instant::now() + WALL;
    let _wall = ScopedSmtDeadline::install_until(end);
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(MEMORY));
    let token = CancellationToken::new();
    let problem = source();
    let mut data = wire(&problem, &token);
    data.graphs[0].nodes[1] = wire::Node::Finite {
        default: wire::Scalar::BitVec {
            width: 8,
            value: "7".into(),
        },
        stores: vec![],
    };
    repin(&problem, &mut data, &token);
    assert!(rebuild::prepare(&problem, &data, &SourceControl::new(end, &token)).is_some());
    let bytes = codec_transport::encode(&data, &SourceControl::new(end, &token)).unwrap();
    assert!(problem
        .validate_complete_trace_artifact(&bytes, remaining(end), Some(MEMORY), &token)
        .is_err());
    assert!(Instant::now() < end);
}

#[test]
#[timeout(30000)]
fn original_r23_stale_witness_roundtrips_whole_array_under_one_twenty_second_end() {
    const ORIGINAL: &str =
        include_str!("../../../../../complete_solve/tests/range_write_refutes_stale_lane_1.smt2");
    let end = Instant::now() + WALL;
    let _wall = ScopedSmtDeadline::install_until(end);
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(MEMORY));
    let token = CancellationToken::new();
    let problem = QuantifiedChcProblem::parse_smtlib(ORIGINAL).unwrap();
    let QuantifiedChcCompleteResult::Unsafe(trace) =
        problem.solve_with_complete_trace(remaining(end), Some(MEMORY), &token)
    else {
        panic!("original canonical full-source complete witness required");
    };
    let bytes = trace
        .export_artifact(&problem, remaining(end), &token)
        .unwrap();
    let imported = problem
        .validate_complete_trace_artifact(&bytes, remaining(end), Some(MEMORY), &token)
        .unwrap();
    assert_eq!(imported.trace().clause_indices(), &[0, 1]);
    assert_eq!(imported.trace().premise_steps(), &[vec![], vec![0]]);
    assert_eq!(
        imported.trace().replay_obligation(),
        trace.replay_obligation()
    );
    assert!(imported.trace().replay_obligation().contains("(forall "));
    let query = imported
        .trace()
        .bindings()
        .iter()
        .find(|entry| entry.occurrence() == 1)
        .unwrap();
    let QuantifiedChcCompleteValue::FunctionalArray(array) = query.value() else {
        panic!("no finite sample substitute");
    };
    assert_scalar_eq(
        &array
            .read_with_stop(&bv(1, 64), &mut 100_000, &mut || {
                token.is_cancelled() || Instant::now() >= end
            })
            .unwrap(),
        &bv(9, 8),
    );
    assert!(Instant::now() < end);
}
