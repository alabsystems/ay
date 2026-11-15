// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Authored source-shaped regressions, not authenticated MC exports.

use super::*;

mod fixtures;
mod oracle;
use fixtures::{loop_source, Cells};

fn solve(
    source: &QuantifiedChcProblem,
    deadline: Instant,
    token: &CancellationToken,
) -> QuantifiedChcCounterexample {
    match source.solve(
        remaining(deadline).min(Duration::from_secs(60)),
        Some(TERM_BUDGET),
        token,
    ) {
        QuantifiedChcResult::Unsafe(evidence) => evidence,
        other => panic!("full original deep derivation must be checked SAT: {other:?}"),
    }
}

/// The counterexample search itself over its own `SEARCH_WINDOW`.
///
/// `solve` hands the search a quarter of its remaining wall (pinned by
/// `solve::function_schedule_tests`), 15 s under the 60 s cap above. The
/// filled-Vec dovetail spends 4.4 s of an idle X925 core's CPU before its
/// depth-11 probe (0.56 s) is SAT; an A725 core needs 1.63x that CPU per
/// probe, so the leader outgrows the shrinking fair share of 15 s and the
/// verdict followed the core the test was scheduled on. What the search
/// reaches is a property of its policy (lazy deepening, retained retries,
/// doubling CPU slices), not of that split; every slice stays CPU-metered.
fn search(
    source: &QuantifiedChcProblem,
    deadline: Instant,
    token: &CancellationToken,
) -> QuantifiedChcCounterexample {
    let until = Instant::now() + remaining(deadline).min(SEARCH_WINDOW);
    let _window = ScopedSmtDeadline::install_until(until);
    super::super::search(source, until, Some(TERM_BUDGET), token)
        .expect("full original deep derivation must be checked SAT")
}

fn linear_edges(count: usize) -> Vec<Vec<usize>> {
    (0..count)
        .map(|step| if step == 0 { vec![] } else { vec![step - 1] })
        .collect()
}

#[test]
fn source_oracle_requires_nine_increments_and_authenticates_the_full_fill_guard() {
    oracle::check();
}

#[test]
#[timeout(180000)]
fn filled_vec_iterator_reaches_position_nine_and_retains_a_complete_typed_trace() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(TERM_BUDGET));
    let deadline = Instant::now() + Duration::from_secs(120);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let token = CancellationToken::new();
    let source = loop_source(Cells::Filled, 8);
    let cpu = ay_sys::thread_clock::ThreadCpuClock::current();
    let cpu_before = cpu.and_then(|clock| clock.elapsed());
    let evidence = search(&source, deadline, &token);
    // The window above no longer bounds the work, so bound it on the search
    // thread's own CPU (its probes run on it; contention does not inflate
    // it): an idle X925 core spends ~7.7 s and an A725 ~1.63x that, under
    // twice the production share (a quarter of the 60 s solve), so a policy
    // change that doubles the search's work fails here on any core.
    let spent = cpu
        .and_then(|clock| clock.elapsed())
        .zip(cpu_before)
        .map(|(after, before)| after.saturating_sub(before));
    if let Some(spent) = spent {
        assert!(
            spent < 2 * Duration::from_secs(15),
            "the filled-Vec search spent {spent:?} of CPU, over twice the production share"
        );
    }
    let mut indices = vec![0];
    indices.extend([1; 9]);
    indices.push(2);
    assert_eq!(evidence.clause_indices(), indices);
    assert_eq!(evidence.premise_steps(), linear_edges(11));
    assert_eq!(
        evidence.replay_obligation().matches("(forall ((").count(),
        10
    );
    assert!(evidence.recheck(&source, remaining(deadline), &token));
    let trace = evidence
        .concrete_trace(&source, remaining(deadline), &token)
        .expect("complete values for this finite record/array trace");
    assert_eq!(trace.clause_indices(), evidence.clause_indices());
    assert_eq!(trace.premise_steps(), evidence.premise_steps());
    assert_eq!(trace.bindings().len(), 21); // fact v; nine (v,pos); query (v,pos)
    for occurrence in 0..11 {
        let bindings: Vec<_> = trace
            .bindings()
            .iter()
            .filter(|binding| binding.occurrence() == occurrence)
            .collect();
        assert_eq!(bindings.len(), if occurrence == 0 { 1 } else { 2 });
        let record = bindings
            .iter()
            .find(|binding| matches!(binding.variable().sort, ChcSort::Datatype { .. }))
            .unwrap();
        oracle::check_record(record.value());
        if occurrence > 0 {
            let position = bindings
                .iter()
                .find(|binding| binding.variable().sort == ChcSort::BitVec(4))
                .unwrap();
            assert_eq!(
                position.value(),
                &SmtValue::BitVec((occurrence - 1) as u128, 4)
            );
        }
    }
    // The BV64 quantified index is lexical, not an occurrence assignment.
    assert!(trace
        .bindings()
        .iter()
        .all(|binding| { binding.variable().sort != ChcSort::BitVec(64) }));
    assert!(trace.recheck(&source, remaining(deadline), &token));
    assert!(Instant::now() < deadline);
}

#[test]
#[timeout(180000)]
fn deep_search_never_omits_a_false_full_premise_or_a_false_final_query() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(TERM_BUDGET));
    let deadline = Instant::now() + Duration::from_secs(120);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    for source in [
        loop_source(Cells::CorruptLast, 8),
        loop_source(Cells::Filled, 7),
    ] {
        assert!(!matches!(
            source.solve(
                remaining(deadline).min(Duration::from_secs(40)),
                Some(TERM_BUDGET),
                &CancellationToken::new(),
            ),
            QuantifiedChcResult::Unsafe(_)
        ));
    }
}

#[test]
#[timeout(180000)]
fn one_query_can_require_eight_independent_body_occurrences() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(TERM_BUDGET));
    let deadline = Instant::now() + Duration::from_secs(120);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let token = CancellationToken::new();
    let source = fixtures::wide_source();
    let evidence = solve(&source, deadline, &token);
    assert_eq!(evidence.clause_indices(), &[0, 0, 0, 0, 0, 0, 0, 0, 1]);
    let mut edges = vec![vec![]; 8];
    edges.push((0..8).collect());
    assert_eq!(evidence.premise_steps(), edges);
    assert_eq!(
        evidence.replay_obligation().matches("(forall ((").count(),
        8
    );
    assert!(evidence.recheck(&source, remaining(deadline), &token));
    assert!(Instant::now() < deadline);
}

#[test]
#[timeout(180000)]
fn a_satisfying_fact_after_sixty_five_decoys_is_not_hidden_by_a_candidate_cap() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(TERM_BUDGET));
    let deadline = Instant::now() + Duration::from_secs(120);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let token = CancellationToken::new();
    let source = fixtures::decoy_source();
    let evidence = solve(&source, deadline, &token);
    assert_eq!(evidence.clause_indices(), &[65, 66]);
    assert_eq!(evidence.premise_steps(), &[vec![], vec![0]]);
    assert_eq!(
        evidence.replay_obligation().matches("(forall ((").count(),
        1
    );
    assert!(evidence.recheck(&source, remaining(deadline), &token));
    assert!(Instant::now() < deadline);
}
