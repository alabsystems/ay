// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::cell::Cell;
use std::panic::{catch_unwind, AssertUnwindSafe};

fn grid() -> Vec<Vec<Literal>> {
    [(1, 2), (1, -2), (-1, 2), (-1, -2)]
        .into_iter()
        .map(|(a, b)| vec![Literal::from_dimacs(a), Literal::from_dimacs(b)])
        .collect()
}

// Independent copy of the previous ordinary path, not the new compatibility
// wrapper (which now deliberately shares the controlled implementation).
fn compatibility_once(
    clauses: &[Vec<Literal>],
    mode: Inprocessing,
) -> Option<Result<ResolutionDag, ResolutionDagError>> {
    let mut solver = Solver::with_proof_output(
        2,
        ProofOutput::lrat_text(Vec::<u8>::new(), clauses.len() as u64),
    );
    solver.set_preprocess_enabled(false);
    if mode == Inprocessing::HintAuthorityRetry {
        solver.disable_all_inprocessing();
    }
    for clause in clauses {
        solver.add_clause(clause.clone());
    }
    match solver.solve().into_inner() {
        SatResult::Unsat(_) => {}
        SatResult::Sat(_) => return Some(Err(ResolutionDagError::Satisfiable)),
        SatResult::Unknown => {
            if solver.last_unknown_reason() == Some(SatUnknownReason::ProofFinalizationFailure)
                && solver
                    .last_unknown_detail()
                    .is_some_and(|detail| detail.contains("LRAT authority fail-closed"))
            {
                return None;
            }
            return Some(Err(ResolutionDagError::Unknown));
        }
    }
    let bytes = solver
        .take_proof_writer()
        .expect("original writer")
        .into_vec()
        .expect("original extraction");
    let text = String::from_utf8(bytes).expect("original text");
    let originals = clauses
        .iter()
        .enumerate()
        .map(|(i, c)| (i as u64 + 1, c.clone()))
        .collect();
    Some(parse_lrat_text_into_dag(2, originals, &text))
}

fn compatibility(clauses: &[Vec<Literal>]) -> Result<ResolutionDag, ResolutionDagError> {
    compatibility_once(clauses, Inprocessing::Ordinary)
        .or_else(|| compatibility_once(clauses, Inprocessing::HintAuthorityRetry))
        .unwrap_or(Err(ResolutionDagError::Unknown))
}

#[test]
fn accepting_control_preserves_the_independent_ordinary_producer() {
    for cnf in [grid(), vec![vec![Literal::from_dimacs(1)]]] {
        let expected = compatibility(&cnf);
        let actual = prove_unsat_resolution_dag_with_cancellation(2, &cnf, &mut || true);
        assert_eq!(
            actual,
            expected
                .clone()
                .map_err(ResolutionDagCancellationError::Resolution)
        );
        assert_eq!(prove_unsat_resolution_dag(2, &cnf), expected);
        if let Ok(dag) = actual {
            dag.validate().expect("independent RUP replay");
        }
    }
}

#[test]
fn until_adapter_preserves_ordinary_sat_and_unsat_results() {
    for cnf in [grid(), vec![vec![Literal::from_dimacs(1)]]] {
        assert_eq!(
            prove_unsat_resolution_dag_until(2, &cnf, &|| false),
            compatibility(&cnf),
        );
    }
}

#[test]
fn until_adapter_keeps_every_observed_stop_sticky_through_publication() {
    let cnf = grid();
    let calls = Cell::new(0usize);
    let dag = prove_unsat_resolution_dag_until(2, &cnf, &|| {
        calls.set(calls.get() + 1);
        false
    })
    .expect("ordinary proof");
    dag.validate().expect("independent replay");
    let total = calls.get();
    assert!(total > 2 && total < 20_000);
    for stop in 1..=total {
        calls.set(0);
        let result = prove_unsat_resolution_dag_until(2, &cnf, &|| {
            calls.set(calls.get() + 1);
            calls.get() == stop
        });
        assert_eq!(
            result,
            Err(ResolutionDagError::Unknown),
            "poll {stop}/{total}"
        );
        assert_eq!(calls.get(), stop, "a later false cannot renew this call");
    }
}

#[test]
fn every_public_observation_including_post_cleanup_refuses_the_proof() {
    let cnf = grid();
    let mut total = 0;
    let expected = prove_unsat_resolution_dag_with_cancellation(2, &cnf, &mut || {
        total += 1;
        true
    })
    .expect("ordinary proof");
    expected.validate().expect("independent replay");
    assert!(total > 2 && total < 20_000);
    for stop in 1..=total {
        let mut calls = 0;
        let result = prove_unsat_resolution_dag_with_cancellation(2, &cnf, &mut || {
            calls += 1;
            calls != stop
        });
        assert_eq!(
            result,
            Err(ResolutionDagCancellationError::Cancelled),
            "poll {stop}/{total}"
        );
        assert_eq!(
            calls, stop,
            "the same false-to-true callback cannot resurrect this call"
        );
    }
}

fn actual_child_trace(mode: Inprocessing) {
    let cnf = grid();
    let mut solver = Solver::with_proof_output(
        2,
        ProofOutput::lrat_text(Vec::<u8>::new(), cnf.len() as u64),
    );
    solver.set_preprocess_enabled(false);
    if mode == Inprocessing::HintAuthorityRetry {
        solver.disable_all_inprocessing();
    }
    for clause in &cnf {
        solver.add_clause(clause.clone());
    }
    let child = Cell::new(0usize);
    assert!(matches!(
        solver
            .solve_interruptible(|| {
                child.set(child.get() + 1);
                false
            })
            .into_inner(),
        SatResult::Unsat(_)
    ));
    let writer = solver.take_proof_writer().expect("same original writer");
    let flush = Cell::new(0usize);
    let inner = writer
        .into_inner_with_cancellation(&|| {
            flush.set(flush.get() + 1);
            true
        })
        .expect("same flush");
    assert!(inner.into_vec().is_some());
    assert!(child.get() > 0, "the actual child must observe its caller");
    let calls = Cell::new(0usize);
    let mut callback = || {
        calls.set(calls.get() + 1);
        true
    };
    let control = ProofControl::new(&mut callback);
    let Attempt::Done(Ok(dag)) = once(2, &cnf, mode, &control) else {
        panic!("same child refutes")
    };
    dag.validate().expect("independent RUP replay");
    assert_eq!(calls.get(), 7 + 4 * cnf.len() + child.get() + flush.get());
}

#[test]
fn the_actual_inprocessing_on_child_inherits_its_owner() {
    actual_child_trace(Inprocessing::Ordinary);
}

#[test]
fn the_actual_no_inprocessing_retry_child_inherits_the_same_owner() {
    actual_child_trace(Inprocessing::HintAuthorityRetry);
}

#[test]
fn a_synthetic_hint_authority_transition_reaches_the_actual_retry_child() {
    let cnf = grid();
    let calls = Cell::new(0usize);
    let mut callback = || {
        calls.set(calls.get() + 1);
        true
    };
    let control = ProofControl::new(&mut callback);
    let mut modes = Vec::new();
    let dag = attempts(&control, |mode, owner| {
        // Compare the thin owner address without unifying callback lifetimes.
        assert!(std::ptr::addr_eq(owner, &control));
        modes.push(mode);
        if mode == Inprocessing::Ordinary {
            Attempt::LratAuthorityFailClosed
        } else {
            once(2, &cnf, mode, owner)
        }
    })
    .expect("actual retry proof after synthetic authority boundary");
    dag.validate().expect("independent RUP replay");
    assert_eq!(
        modes,
        [Inprocessing::Ordinary, Inprocessing::HintAuthorityRetry]
    );
    assert!(calls.get() > 1);
}

#[test]
fn an_owner_refusal_at_the_authority_transition_cannot_start_the_retry() {
    let mut calls = 0;
    let mut callback = || {
        calls += 1;
        calls != 1
    };
    let control = ProofControl::new(&mut callback);
    let mut attempts_started = 0;
    let result = attempts(&control, |mode, _| {
        attempts_started += 1;
        assert_eq!(mode, Inprocessing::Ordinary);
        Attempt::LratAuthorityFailClosed
    });
    assert_eq!(result, Err(ResolutionDagError::Unknown));
    assert!(control.check_latched().is_err());
    assert_eq!(attempts_started, 1);
    drop(control);
    assert_eq!(calls, 1);
}

#[test]
fn an_owner_refusal_inside_the_actual_retry_child_is_sticky() {
    let cnf = grid();
    let calls = Cell::new(0usize);
    let mut callback = || {
        calls.set(calls.get() + 1);
        calls.get() != 12
    };
    let control = ProofControl::new(&mut callback);
    let mut modes = Vec::new();
    let result = attempts(&control, |mode, owner| {
        modes.push(mode);
        if mode == Inprocessing::Ordinary {
            Attempt::LratAuthorityFailClosed
        } else {
            once(2, &cnf, mode, owner)
        }
    });
    // 1 authority-boundary poll + 1 child entry + 8 clause-copy observations
    // + 1 pre-solve poll: the twelfth is an actual solver observation.
    assert_eq!(result, Err(ResolutionDagError::Unknown));
    assert!(control.check_latched().is_err());
    assert_eq!(calls.get(), 12);
    assert_eq!(
        modes,
        [Inprocessing::Ordinary, Inprocessing::HintAuthorityRetry]
    );
    assert!(matches!(
        once(2, &cnf, Inprocessing::Ordinary, &control),
        Attempt::Done(Err(ResolutionDagError::Unknown))
    ));
    assert_eq!(calls.get(), 12);
}

#[test]
fn an_ordinary_error_does_not_select_a_retry_or_invoke_a_new_callback() {
    let mut callback = || panic!("an already reached error must not repoll");
    let control = ProofControl::new(&mut callback);
    let mut started = 0;
    let result = attempts(&control, |mode, _| {
        started += 1;
        assert_eq!(mode, Inprocessing::Ordinary);
        Attempt::Done(Err(ResolutionDagError::Satisfiable))
    });
    assert_eq!(result, Err(ResolutionDagError::Satisfiable));
    assert_eq!(started, 1);
}

#[test]
fn a_caught_observer_unwind_cannot_restart_either_actual_child() {
    let cnf = grid();
    let calls = Cell::new(0usize);
    let mut callback = || {
        calls.set(calls.get() + 1);
        panic!("observer unwind");
    };
    let control = ProofControl::new(&mut callback);
    assert!(catch_unwind(AssertUnwindSafe(|| once(
        2,
        &cnf,
        Inprocessing::Ordinary,
        &control
    )))
    .is_err());
    for mode in [Inprocessing::Ordinary, Inprocessing::HintAuthorityRetry] {
        assert!(matches!(
            once(2, &cnf, mode, &control),
            Attempt::Done(Err(ResolutionDagError::Unknown))
        ));
    }
    assert_eq!(calls.get(), 1);
}
