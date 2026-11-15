// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::original_query::{
    FiniteAdmissionGrant, OriginalAdmission, OriginalAdmissionError, QueryError, WorkBudget,
};
use std::cell::Cell;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

mod fences;
mod ownership;

fn end() -> Instant {
    Instant::now() + Duration::from_secs(20)
}

fn fixture(end: Instant, source: &str) -> (Solver, ExactSmtlibQueryBinding) {
    assert!(Instant::now() < end);
    let (mut solver, binding) = parsed(Logic::All, source, Presentation::StrictWire);
    solver.set_timeout(Some(end.saturating_duration_since(Instant::now())));
    assert!(solver.check_sat().is_unsat());
    assert!(Instant::now() < end);
    (solver, binding)
}

fn offers(solver: &Solver, binding: &ExactSmtlibQueryBinding, end: Instant) -> Vec<(usize, usize)> {
    let mut result = Vec::new();
    assert!(solver
        .export_last_unsat_retained_bundle_for_exact_query_with_resource_control(
            binding,
            end,
            &mut |work, bytes| {
                assert!(Instant::now() < end);
                result.push((work, bytes));
                true
            },
        )
        .unwrap()
        .is_some());
    result
}

fn cost(solver: &Solver, binding: &ExactSmtlibQueryBinding, end: Instant) -> (usize, usize) {
    let (work, bytes) = totals(&offers(solver, binding, end));
    (work.checked_add(8).unwrap(), bytes)
}

fn owner(work: usize, bytes: usize, end: Instant) -> OriginalAdmission {
    OriginalAdmission::new(
        FiniteAdmissionGrant::new(u64::try_from(work).unwrap(), bytes),
        end,
        Arc::new(|| false),
    )
}

fn admitted(
    owner: &OriginalAdmission,
    solver: &Solver,
    binding: &ExactSmtlibQueryBinding,
    end: Instant,
) -> Result<Option<()>, OriginalAdmissionError> {
    owner.with_work(|work| {
        match solver.with_last_unsat_retained_bundle_for_exact_query_with_work(
            binding,
            end,
            work,
            |_, _| Ok(()),
        ) {
            Ok(value) => Ok(value),
            Err(ProofCheckError::ResourceLimit) => Err(work.refuse_exhaustion()),
            Err(_) => Err(QueryError::Invalid("retained strict export rejected")),
        }
    })
}

#[test]
fn scoped_export_forwards_exact_legacy_offers_then_cleanup_poll() {
    let end = end();
    let (solver, binding) = fixture(end, BOOLEAN);
    let legacy = offers(&solver, &binding, end);
    assert!(legacy.iter().any(|&(w, b)| w > 0 && b > 0));
    assert!(legacy.contains(&(0, 0)));
    let mut actual = Vec::new();
    let mut sink = |work, bytes| {
        assert!(Instant::now() < end);
        actual.push((work, bytes));
        Ok(())
    };
    let mut work = WorkBudget::with_admission(u64::MAX, &mut sink);
    let mut consumed = false;
    assert_eq!(
        solver
            .with_last_unsat_retained_bundle_for_exact_query_with_work(
                &binding,
                end,
                &mut work,
                |bundle, _| {
                    assert_eq!(bundle.schema(), "ay.proofbundle/v6");
                    assert!(!bundle.obligation_assertions().is_empty());
                    consumed = true;
                    Ok(())
                },
            )
            .unwrap(),
        Some(())
    );
    drop(work);
    let mut expected = vec![(8, 0)];
    expected.extend(legacy);
    expected.push((0, 0));
    expected.push((0, 0));
    assert_eq!(actual, expected);
    assert!(consumed);
}

#[test]
fn scoped_export_replays_the_actual_folded_source_on_same_adapter() {
    let end = end();
    let (solver, binding) = fixture(end, FOLDED);
    let mut sink = |_, _| {
        if Instant::now() < end {
            Ok(())
        } else {
            Err(QueryError::Interrupted(
                ay_core::original_query::StopReason::Deadline,
            ))
        }
    };
    let mut work = WorkBudget::with_admission(u64::MAX, &mut sink);
    assert_eq!(
        solver
            .with_last_unsat_retained_bundle_for_exact_query_with_work(
                &binding,
                end,
                &mut work,
                |bundle, work| {
                    let checked = bundle.replay_exact_with_resource_control(end, &mut |w, b| {
                        work.admit(w, b).is_ok()
                    })?;
                    assert!(checked.quality.is_complete());
                    assert_eq!(checked.assume_terms, bundle.obligation_assertions());
                    assert_ne!(
                        bundle.obligation_assertions(),
                        binding
                            .assertions()
                            .iter()
                            .map(|term| term.id())
                            .collect::<Vec<_>>()
                    );
                    Ok(())
                },
            )
            .unwrap(),
        Some(())
    );
}

#[test]
fn foreign_binding_declines_without_consumption_or_owner_exhaustion() {
    let end = end();
    let (solver, binding) = fixture(end, BOOLEAN);
    let (_, foreign) = fixture(end, BOOLEAN);
    let admission = owner(usize::MAX / 4, usize::MAX / 4, end);
    assert_eq!(
        admission.with_work(|work| {
            let result = solver.with_last_unsat_retained_bundle_for_exact_query_with_work(
                &foreign,
                end,
                work,
                |_, _| panic!("foreign source must not reach the consumer"),
            );
            assert!(matches!(result, Ok(None)));
            work.charge(0)?;
            Ok(())
        }),
        Ok(())
    );
    assert_eq!(admitted(&admission, &solver, &binding, end), Ok(Some(())));
}

#[test]
fn preconsumption_zero_poll_refuses_before_the_user_callback() {
    let end = end();
    let (solver, binding) = fixture(end, BOOLEAN);
    let legacy = offers(&solver, &binding, end);
    let mut calls = 0usize;
    let mut sink = |_, _| {
        assert!(Instant::now() < end);
        calls += 1;
        if calls == legacy.len() + 2 {
            Err(QueryError::Interrupted(
                ay_core::original_query::StopReason::Cancelled,
            ))
        } else {
            Ok(())
        }
    };
    let mut work = WorkBudget::with_admission(u64::MAX, &mut sink);
    let mut consumed = false;
    assert!(matches!(
        solver.with_last_unsat_retained_bundle_for_exact_query_with_work(
            &binding,
            end,
            &mut work,
            |_, _| {
                consumed = true;
                Ok(())
            },
        ),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert_eq!(
        work.charge(0),
        Err(QueryError::Interrupted(
            ay_core::original_query::StopReason::Cancelled
        ))
    );
    drop(work);
    assert!(!consumed);
    assert_eq!(calls, legacy.len() + 2);
}
