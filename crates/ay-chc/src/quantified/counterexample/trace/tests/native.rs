// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

const MEMORY: usize = 128 * 1024 * 1024;

fn remaining(deadline: Instant) -> Duration {
    deadline.saturating_duration_since(Instant::now())
}

fn evidence(
    source: &QuantifiedChcProblem,
    deadline: Instant,
    token: &CancellationToken,
) -> QuantifiedChcCounterexample {
    match source.solve(
        remaining(deadline).min(Duration::from_secs(45)),
        Some(MEMORY),
        token,
    ) {
        QuantifiedChcResult::Unsafe(value) => value,
        other => panic!("expected original-source checked Unsafe: {other:?}"),
    }
}

#[test]
#[timeout(180000)]
fn concrete_scalar_trace_is_owned_complete_and_refuses_another_satisfying_assignment() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(MEMORY));
    let deadline = Instant::now() + Duration::from_secs(120);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let token = CancellationToken::new();
    let source = scalar_source();
    let base = evidence(&source, deadline, &token);
    let mut trace = base
        .concrete_trace(&source, remaining(deadline), &token)
        .unwrap();
    drop(base);
    assert_eq!(trace.source_smtlib(), source.source_smtlib());
    assert_eq!(trace.clause_indices(), &[0, 0, 1]);
    assert_eq!(trace.premise_steps(), &[vec![], vec![], vec![0, 1]]);
    assert_eq!(trace.bindings().len(), 4);
    let row: Vec<_> = trace
        .bindings()
        .iter()
        .map(|binding| {
            assert!(binding.occurrence() < 3);
            assert_eq!(binding.variable().sort, ChcSort::BitVec(2));
            let SmtValue::BitVec(value, 2) = binding.value() else {
                panic!("exact scalar")
            };
            *value as u64
        })
        .collect();
    assert_eq!(oracle::models(trace.replay_obligation()), vec![row]);
    assert!(trace.recheck(&source, remaining(deadline), &token));
    // Add one modulo four to ALL values: still a satisfying assignment, but
    // it is not this construction-sealed retained witness.
    for binding in &mut trace.bindings {
        let SmtValue::BitVec(value, 2) = &mut binding.value else {
            panic!("exact scalar")
        };
        *value = (*value + 1) % 4;
    }
    let rendered = bound_render(&trace.base, &source, &control(&token)).unwrap();
    let registry = registry(&source, &control(&token)).unwrap();
    let changed = pins::render(
        &rendered,
        &trace.bindings,
        &trace.functions,
        &source,
        &registry,
        &control(&token),
    )
    .unwrap();
    assert_eq!(oracle::models(&changed).len(), 1);
    assert!(!trace.recheck(&source, remaining(deadline), &token));
}

fn vec_source() -> QuantifiedChcProblem {
    // Authored producer-shaped composition, not an authenticated MC export.
    QuantifiedChcProblem::parse_smtlib(
        "(set-logic HORN)
         (declare-datatype Vec ((mkVec (ptr (_ BitVec 64)) (len (_ BitVec 64))
           (cap (_ BitVec 64)) (data (Array (_ BitVec 64) (_ BitVec 8))))))
         (declare-fun P (Vec (_ BitVec 8)) Bool)
         (assert (forall ((v Vec) (f (_ BitVec 8)))
           (=> (and (= v (mkVec (_ bv0 64) (_ bv65 64) (_ bv65 64)
                       ((as const (Array (_ BitVec 64) (_ BitVec 8))) f)))
                    (forall ((i (_ BitVec 64)))
                       (=> (bvult i (len v)) (= (select (data v) i) f)))) (P v f))))
         (assert (forall ((a Vec) (b Vec))
           (=> (and (P a (_ bv7 8)) (P b (_ bv9 8))
                    (distinct (select (data a) (_ bv64 64))
                              (select (data b) (_ bv64 64)))) false)))
         (check-sat)",
    )
    .unwrap()
}

#[test]
#[timeout(300000)]
fn full_vec_values_replay_and_corrupted_last_cell_cannot_fall_back_to_unpinned_sat() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(MEMORY));
    let deadline = Instant::now() + Duration::from_secs(240);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let token = CancellationToken::new();
    let source = vec_source();
    let base = evidence(&source, deadline, &token);
    let mut trace = base
        .concrete_trace(&source, remaining(deadline), &token)
        .unwrap();
    assert_eq!(trace.bindings().len(), 6);
    assert_eq!(trace.replay_obligation().matches("(forall ((").count(), 2);
    assert!(trace.replay_obligation().contains("(_ bv64 64)"));
    assert!(trace.recheck(&source, remaining(deadline), &token));
    for occurrence in [0, 1] {
        let fill = trace
            .bindings()
            .iter()
            .find(|binding| {
                binding.occurrence() == occurrence && binding.variable().sort == ChcSort::BitVec(8)
            })
            .unwrap();
        assert_eq!(
            fill.value(),
            &SmtValue::BitVec(if occurrence == 0 { 7 } else { 9 }, 8)
        );
    }
    let record = trace
        .bindings
        .iter_mut()
        .find(|binding| binding.occurrence == 0 && matches!(binding.value, SmtValue::Datatype(..)))
        .unwrap();
    let SmtValue::Datatype(constructor, fields) = &mut record.value else {
        unreachable!()
    };
    assert_eq!(constructor, "mkVec");
    assert_eq!(fields.len(), 4);
    assert_eq!(
        &fields[..3],
        &[
            SmtValue::BitVec(0, 64),
            SmtValue::BitVec(65, 64),
            SmtValue::BitVec(65, 64)
        ]
    );
    let SmtValue::ArrayMap { entries, .. } = &mut fields[3] else {
        panic!("complete ordered array")
    };
    entries.push((SmtValue::BitVec(64, 64), SmtValue::BitVec(8, 8)));
    // Even after a test-only attacker recomputes the exact pins, the bad
    // concrete value must fail full SAT. The unpinned existential base remains
    // satisfiable and MUST NOT be used as a replay fallback.
    let rendered = bound_render(&trace.base, &source, &control(&token)).unwrap();
    let registry = registry(&source, &control(&token)).unwrap();
    trace.pinned_obligation = pins::render(
        &rendered,
        &trace.bindings,
        &trace.functions,
        &source,
        &registry,
        &control(&token),
    )
    .unwrap();
    assert!(!trace.recheck(&source, remaining(deadline), &token));
    assert!(base.recheck(&source, remaining(deadline), &token));
}

#[test]
#[timeout(180000)]
fn empty_local_trace_retains_query_and_refuses_cancelled_zero_and_parent_budgets() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(MEMORY));
    let deadline = Instant::now() + Duration::from_secs(90);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let token = CancellationToken::new();
    let source =
        QuantifiedChcProblem::parse_smtlib("(set-logic HORN) (assert false) (check-sat)").unwrap();
    let base = evidence(&source, deadline, &token);
    let trace = base
        .concrete_trace(&source, remaining(deadline), &token)
        .unwrap();
    assert_eq!(trace.clause_indices(), &[0]);
    assert_eq!(trace.premise_steps(), &[Vec::<usize>::new()]);
    assert!(trace.bindings().is_empty());
    assert!(trace.recheck(&source, remaining(deadline), &token));
    assert!(!trace.recheck(&source, Duration::ZERO, &token));
    token.cancel();
    assert!(!trace.recheck(&source, remaining(deadline), &token));
    assert!(base
        .concrete_trace(&source, remaining(deadline), &token)
        .is_none());
    token.reset();
    {
        let _zero = SmtContext::scoped_thread_term_memory_budget(Some(0));
        assert!(!trace.recheck(&source, remaining(deadline), &token));
        assert!(base
            .concrete_trace(&source, remaining(deadline), &token)
            .is_none());
    }
    assert!(trace.recheck(&source, remaining(deadline), &token));
}
