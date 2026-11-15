// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::original_query::FiniteAdmissionGrant;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Arc;

mod extensions;
mod propagation;

fn owner(work: u64) -> CountedAdmission {
    CountedAdmission::new(
        FiniteAdmissionGrant::new(work, 1 << 20),
        None,
        Arc::new(|| false),
    )
    .unwrap()
}

fn empty_case(unsat: bool) -> Solver {
    let mut solver = Solver::new(0);
    if unsat {
        assert!(!solver.add_clause(Vec::new()));
    }
    solver
}

fn attach(solver: &mut Solver, owner: &CountedAdmission) {
    assert!(solver.attach_counted_admission(owner.clone()).is_ok());
}

fn definitive(result: SatResult, unsat: bool) {
    if unsat {
        assert!(matches!(result, SatResult::Unsat(_)));
    } else {
        assert!(matches!(result, SatResult::Sat(_)));
    }
}

#[test]
fn zero_effort_cannot_decide_empty_sat_or_empty_clause_unsat() {
    for unsat in [false, true] {
        let mut solver = empty_case(unsat);
        let original = owner(0);
        attach(&mut solver, &original);
        assert!(matches!(solver.solve().into_inner(), SatResult::Unknown));
        assert_eq!(
            solver.last_unknown_reason(),
            Some(SatUnknownReason::ResourceBudget)
        );
        assert_eq!(original.usage().unwrap().work_admitted, 0);
        assert_eq!(original.check(), Err(CountedAdmissionError::WorkExhausted));
    }
}

#[test]
fn actual_entry_and_publication_cost_has_exact_and_short_controls() {
    for unsat in [false, true] {
        let mut baseline = empty_case(unsat);
        let original = owner(1000);
        attach(&mut baseline, &original);
        definitive(baseline.solve().into_inner(), unsat);
        let used = original.usage().unwrap().work_admitted;
        assert!(used >= 2);
        for grant in [used - 1, used] {
            let mut solver = empty_case(unsat);
            let original = owner(grant);
            attach(&mut solver, &original);
            let result = solver.solve().into_inner();
            if grant == used {
                definitive(result, unsat);
                assert_eq!(original.usage().unwrap().work_remaining, 0);
            } else {
                assert!(matches!(result, SatResult::Unknown));
                assert_eq!(original.check(), Err(CountedAdmissionError::WorkExhausted));
            }
        }
    }
}

#[test]
fn repeated_solves_and_clones_share_credit_and_cannot_replace_it() {
    let mut solver = empty_case(false);
    let original = owner(4);
    attach(&mut solver, &original);
    let mut clone = solver.clone_for_incremental();
    definitive(solver.solve().into_inner(), false);
    definitive(clone.solve().into_inner(), false);
    assert_eq!(original.usage().unwrap().work_admitted, 4);
    let fresh = owner(100);
    let rejected = solver.attach_counted_admission(fresh.clone());
    assert!(rejected.is_err());
    assert!(matches!(solver.solve().into_inner(), SatResult::Unknown));
    assert!(matches!(clone.solve().into_inner(), SatResult::Unknown));
    assert_eq!(fresh.usage().unwrap().work_admitted, 0);
    assert_eq!(
        solver.counted_admission_usage().unwrap().unwrap().refusal,
        Some(CountedAdmissionError::WorkExhausted)
    );
}

#[test]
fn refusal_at_final_verdict_fence_withholds_both_results() {
    for unsat in [false, true] {
        let mut solver = empty_case(unsat);
        let calls = Arc::new(AtomicUsize::new(0));
        let observed = Arc::clone(&calls);
        let original = CountedAdmission::new(
            FiniteAdmissionGrant::new(100, 100),
            None,
            Arc::new(move || observed.fetch_add(1, Ordering::SeqCst) == 1),
        )
        .unwrap();
        attach(&mut solver, &original);
        let result = if unsat {
            solver.declare_unsat()
        } else {
            solver.declare_sat_from_model(Vec::new())
        };
        assert!(matches!(result, SatResult::Unknown));
        assert_eq!(original.usage().unwrap().work_admitted, 1);
        assert_eq!(
            original.check(),
            Err(CountedAdmissionError::Original(
                OriginalAdmissionError::ObserverStopped
            ))
        );
        assert!(matches!(solver.solve().into_inner(), SatResult::Unknown));
    }
}

#[test]
fn a_one_shot_solve_callback_refusal_cannot_be_reset_for_retry() {
    let mut solver = empty_case(false);
    let original = owner(100);
    attach(&mut solver, &original);
    let armed = AtomicBool::new(true);
    assert!(matches!(
        solver
            .solve_interruptible(|| armed.swap(false, Ordering::SeqCst))
            .into_inner(),
        SatResult::Unknown
    ));
    assert!(!armed.load(Ordering::SeqCst));
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::Interrupted)
    );
    assert!(matches!(solver.solve().into_inner(), SatResult::Unknown));
}

struct StopOnDrop(Arc<AtomicBool>);
impl Drop for StopOnDrop {
    fn drop(&mut self) {
        self.0.store(true, Ordering::SeqCst);
    }
}

#[test]
fn callback_cleanup_before_public_return_can_veto_sat_and_unsat() {
    for unsat in [false, true] {
        let stopped = Arc::new(AtomicBool::new(false));
        let observed = Arc::clone(&stopped);
        let original = CountedAdmission::new(
            FiniteAdmissionGrant::new(100, 100),
            None,
            Arc::new(move || observed.load(Ordering::SeqCst)),
        )
        .unwrap();
        let mut solver = empty_case(unsat);
        attach(&mut solver, &original);
        let cleanup = StopOnDrop(Arc::clone(&stopped));
        let result = solver.solve_interruptible(move || {
            let _retained = &cleanup;
            false
        });
        assert!(stopped.load(Ordering::SeqCst));
        assert!(matches!(result.into_inner(), SatResult::Unknown));
        assert_eq!(
            solver.last_unknown_reason(),
            Some(SatUnknownReason::Interrupted)
        );
    }
}

#[test]
fn contradictory_units_and_assumptions_have_zero_and_healthy_controls() {
    for grant in [0, 1000] {
        let mut solver = Solver::new(1);
        let x = Literal::positive(Variable::new(0));
        solver.add_clause(vec![x]);
        solver.add_clause(vec![x.negated()]);
        attach(&mut solver, &owner(grant));
        let result = solver.solve().into_inner();
        if grant == 0 {
            assert!(matches!(result, SatResult::Unknown));
        } else {
            definitive(result, true);
        }

        let mut solver = Solver::new(1);
        solver.add_clause(vec![x]);
        attach(&mut solver, &owner(grant));
        let result = solver.solve_with_assumptions(&[x.negated()]).into_inner();
        if grant == 0 {
            assert!(matches!(result, AssumeResult::Unknown));
        } else {
            assert!(matches!(result, AssumeResult::Unsat(..)));
        }
    }
}

#[test]
fn proof_progress_refusal_and_panic_are_terminal_for_the_same_owner() {
    for panic in [false, true] {
        let mut solver = empty_case(true);
        let original = owner(100);
        attach(&mut solver, &original);
        assert!(!solver.counted_proof_progress(&|| {
            assert!(!panic, "test proof observer panic");
            false
        }));
        assert!(original.usage().unwrap().refusal.is_some());
        assert!(!solver.counted_proof_progress(&|| true));
        assert!(matches!(solver.solve().into_inner(), SatResult::Unknown));
    }
    let mut healthy = empty_case(true);
    let original = owner(100);
    attach(&mut healthy, &original);
    assert!(healthy.counted_proof_progress(&|| true));
    definitive(healthy.solve().into_inner(), true);
}

#[test]
fn borrowed_solve_callback_panic_is_terminal_without_revival() {
    let mut solver = empty_case(false);
    let original = owner(100);
    attach(&mut solver, &original);
    assert!(matches!(
        solver
            .solve_interruptible(|| panic!("borrowed solve callback"))
            .into_inner(),
        SatResult::Unknown
    ));
    assert_eq!(
        original.usage().unwrap().refusal,
        Some(CountedAdmissionError::Original(
            OriginalAdmissionError::OperationPanicked
        ))
    );
    assert!(matches!(solver.solve().into_inner(), SatResult::Unknown));
}

#[test]
fn owned_assumption_callback_is_dropped_before_the_counted_final_fence() {
    for ic3 in [false, true] {
        for unsat in [false, true] {
            let stopped = Arc::new(AtomicBool::new(false));
            let observed = Arc::clone(&stopped);
            let original = CountedAdmission::new(
                FiniteAdmissionGrant::new(1000, 1000),
                None,
                Arc::new(move || observed.load(Ordering::SeqCst)),
            )
            .unwrap();
            let mut solver = empty_case(unsat);
            if ic3 {
                solver.set_ic3_mode();
            }
            attach(&mut solver, &original);
            let cleanup = StopOnDrop(Arc::clone(&stopped));
            let stop = move || {
                let _retained = &cleanup;
                false
            };
            let result = if ic3 {
                solver.solve_incremental_ic3_interruptible(&[], stop)
            } else {
                solver.solve_with_assumptions_interruptible(&[], stop)
            };
            assert!(stopped.load(Ordering::SeqCst));
            assert!(matches!(result.into_inner(), AssumeResult::Unknown));
            assert!(original.usage().unwrap().refusal.is_some());
        }
    }
}
