// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

struct OnDrop(Arc<AtomicBool>);

impl Drop for OnDrop {
    fn drop(&mut self) {
        self.0.store(true, Ordering::SeqCst);
    }
}

#[test]
fn original_callback_reset_cannot_revive_after_consumption_stop() {
    let end = end();
    let (solver, binding) = fixture(end, BOOLEAN);
    let stopped = Arc::new(AtomicBool::new(false));
    let observed = stopped.clone();
    let admission = OriginalAdmission::new(
        FiniteAdmissionGrant::new(u64::MAX, usize::MAX),
        end,
        Arc::new(move || observed.load(Ordering::SeqCst)),
    );
    let consumed = Cell::new(false);
    assert_eq!(
        admission.with_work(|work| {
            assert!(matches!(
                solver.with_last_unsat_retained_bundle_for_exact_query_with_work(
                    &binding,
                    end,
                    work,
                    |_, _| {
                        consumed.set(true);
                        stopped.store(true, Ordering::SeqCst);
                        Ok(())
                    },
                ),
                Err(ProofCheckError::ResourceLimit)
            ));
            work.charge(0)
        }),
        Err(OriginalAdmissionError::ObserverStopped)
    );
    assert!(consumed.get());
    stopped.store(false, Ordering::SeqCst);
    assert_eq!(
        admitted(&admission.clone(), &solver, &binding, end),
        Err(OriginalAdmissionError::ObserverStopped)
    );
}

#[test]
fn final_fence_observes_consumer_environment_drop_without_erasing_completed_fact() {
    let end = end();
    let (solver, binding) = fixture(end, BOOLEAN);
    let dropped = Arc::new(AtomicBool::new(false));
    let observed = dropped.clone();
    let admission = OriginalAdmission::new(
        FiniteAdmissionGrant::new(u64::MAX, usize::MAX),
        end,
        Arc::new(move || observed.load(Ordering::SeqCst)),
    );
    let guard = OnDrop(dropped.clone());
    let completed = Cell::new(false);
    assert_eq!(
        admission.with_work(|work| {
            let completed = &completed;
            assert!(matches!(
                solver.with_last_unsat_retained_bundle_for_exact_query_with_work(
                    &binding,
                    end,
                    work,
                    move |bundle, _| {
                        assert_eq!(bundle.schema(), "ay.proofbundle/v6");
                        let _retain_until_callback_returns = &guard;
                        completed.set(true);
                        Ok(())
                    },
                ),
                Err(ProofCheckError::ResourceLimit)
            ));
            work.charge(0)
        }),
        Err(OriginalAdmissionError::ObserverStopped)
    );
    assert!(dropped.load(Ordering::SeqCst));
    assert!(completed.get());
    assert!(solver
        .export_last_unsat_retained_bundle_for_exact_query_with_resource_control(
            &binding,
            end,
            &mut |_, _| Instant::now() < end,
        )
        .unwrap()
        .is_some());
}

#[test]
fn consumer_replay_one_short_revokes_future_consumption_not_prior_proof() {
    let end = end();
    let (solver, binding) = fixture(end, BOOLEAN);
    let (units, bytes) = cost(&solver, &binding, end);
    let admission = owner(units, bytes, end);
    let completed = Cell::new(false);
    assert_eq!(
        admission.with_work(|work| {
            let result = solver.with_last_unsat_retained_bundle_for_exact_query_with_work(
                &binding,
                end,
                work,
                |bundle, work| {
                    completed.set(true);
                    bundle.replay_exact_with_resource_control(end, &mut |w, b| {
                        work.admit(w, b).is_ok()
                    })?;
                    Ok(())
                },
            );
            assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
            work.charge(0)
        }),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
    assert!(completed.get());
    assert_eq!(
        admitted(&admission, &solver, &binding, end),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
}

#[test]
fn consumer_panic_drops_local_artifact_and_original_with_work_latches_unwind() {
    let end = end();
    let (solver, binding) = fixture(end, BOOLEAN);
    let admission = owner(usize::MAX / 4, usize::MAX / 4, end);
    let dropped = Arc::new(AtomicBool::new(false));
    let guard = OnDrop(dropped.clone());
    assert_eq!(
        admission.with_work(|work| {
            let _ = solver.with_last_unsat_retained_bundle_for_exact_query_with_work(
                &binding,
                end,
                work,
                move |_, _| {
                    let _retain_until_unwind = &guard;
                    panic!("controlled test consumer unwind")
                },
            );
            Ok(())
        }),
        Err(OriginalAdmissionError::OperationPanicked)
    );
    assert!(dropped.load(Ordering::SeqCst));
    assert_eq!(
        admission.clone().check(),
        Err(OriginalAdmissionError::OperationPanicked)
    );
}
