// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bounded native PB regression guards for timeout-sensitive paths.
//!
//! These tests intentionally stay on public `ay-pb` APIs:
//! - `preprocess()` on a duplicate-heavy linear family
//! - `PbCdclSolver::solve()` on a conflict/backtrack-heavy UNSAT family
//!
//! The goal is not to micro-benchmark exact runtimes. Instead, these tests
//! catch "no-stop" or accidental superlinear regressions by enforcing generous
//! wall-clock budgets on representative workloads that have historically been
//! fragile.

use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

use ay_pb::{
    preprocess, verify_all_constraints, PbCdclResult, PbCdclSolver, PbCdclStats, PbConstraint,
    PbInstance, PbLit, PbRel, PbTerm, PreprocessResult,
};

const PREPROCESS_BUDGET: Duration = Duration::from_secs(5);
const SOLVE_BUDGET: Duration = Duration::from_secs(5);

fn lit(var: u32) -> PbLit {
    PbLit {
        var,
        negated: false,
    }
}

fn not(var: u32) -> PbLit {
    PbLit { var, negated: true }
}

fn linear_term(coeff: i128, pb_lit: PbLit) -> PbTerm {
    PbTerm {
        coeff,
        lits: vec![pb_lit],
    }
}

fn ge_constraint(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
    PbConstraint {
        terms,
        rel: PbRel::Ge,
        rhs,
    }
}

fn duplicate_cardinality_instance(num_duplicates: usize) -> PbInstance {
    let template = ge_constraint((1..=6).map(|var| linear_term(1, lit(var))).collect(), 3);

    PbInstance {
        num_vars: 6,
        num_constraints: num_duplicates as u32,
        constraints: vec![template; num_duplicates],
        objective: None,
    }
}

fn root_probe_decoy_backtracking_instance() -> PbInstance {
    let num_probe_decoys = 4;
    let num_pigeons = 3;
    let num_holes = 2;
    let mut constraints = Vec::new();
    let var_for = |pigeon: u32, hole: u32| num_probe_decoys + (pigeon * num_holes) + hole + 1;

    // Give the bounded root-probe pass four high-activity variables whose
    // single-literal probes only propagate their XOR partner instead of
    // immediately exposing the real UNSAT core.
    constraints.push(ge_constraint(
        vec![linear_term(100, lit(1)), linear_term(100, lit(2))],
        100,
    ));
    constraints.push(ge_constraint(
        vec![linear_term(100, not(1)), linear_term(100, not(2))],
        100,
    ));
    constraints.push(ge_constraint(
        vec![linear_term(100, lit(3)), linear_term(100, lit(4))],
        100,
    ));
    constraints.push(ge_constraint(
        vec![linear_term(100, not(3)), linear_term(100, not(4))],
        100,
    ));

    for pigeon in 0..num_pigeons {
        let terms = (0..num_holes)
            .map(|hole| linear_term(1, lit(var_for(pigeon, hole))))
            .collect();
        constraints.push(ge_constraint(terms, 1));
    }

    for hole in 0..num_holes {
        let terms = (0..num_pigeons)
            .map(|pigeon| linear_term(1, not(var_for(pigeon, hole))))
            .collect();
        constraints.push(ge_constraint(terms, i128::from(num_pigeons) - 1));
    }

    PbInstance {
        num_vars: num_probe_decoys + (num_pigeons * num_holes),
        num_constraints: constraints.len() as u32,
        constraints,
        objective: None,
    }
}

fn weighted_pigeonhole_instance(num_pigeons: u32, num_holes: u32) -> PbInstance {
    assert!(num_pigeons > num_holes);

    let mut constraints = Vec::new();
    let var_for = |pigeon: u32, hole: u32| (pigeon * num_holes) + hole + 1;

    for pigeon in 0..num_pigeons {
        let terms = (0..num_holes)
            .map(|hole| linear_term(2, lit(var_for(pigeon, hole))))
            .collect();
        constraints.push(ge_constraint(terms, 2));
    }

    for hole in 0..num_holes {
        let terms = (0..num_pigeons)
            .map(|pigeon| linear_term(1, not(var_for(pigeon, hole))))
            .collect();
        constraints.push(ge_constraint(terms, i128::from(num_pigeons) - 1));
    }

    PbInstance {
        num_vars: num_pigeons * num_holes,
        num_constraints: constraints.len() as u32,
        constraints,
        objective: None,
    }
}

fn preprocess_bounded(instance: PbInstance) -> PreprocessResult {
    let (tx, rx) = mpsc::channel();

    thread::spawn(move || {
        let _ = tx.send(preprocess(&instance));
    });

    match rx.recv_timeout(PREPROCESS_BUDGET) {
        Ok(result) => result,
        Err(mpsc::RecvTimeoutError::Timeout) => panic!(
            "preprocess() exceeded {PREPROCESS_BUDGET:?} on duplicate-heavy linear PB instance"
        ),
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            panic!("preprocess thread disconnected before reporting a result")
        }
    }
}

fn solve_bounded(instance: PbInstance) -> (PbCdclResult, PbCdclStats) {
    let (tx, rx) = mpsc::channel();

    thread::spawn(move || {
        // Construct unpreprocessed so this regression exercises the CDCL
        // backtracking/conflict-analysis path. Failed-literal probing in
        // preprocessing can now prove this decoy-protected pigeonhole UNSAT at
        // the root, which would otherwise eliminate the decision search the test
        // is specifically guarding.
        let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, || false);
        let result = solver.solve();
        let stats = solver.stats().clone();
        let _ = tx.send((result, stats));
    });

    match rx.recv_timeout(SOLVE_BUDGET) {
        Ok(summary) => summary,
        Err(mpsc::RecvTimeoutError::Timeout) => {
            panic!("native PB solve exceeded {SOLVE_BUDGET:?} on pigeonhole backtracking guard")
        }
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            panic!("solver thread disconnected before reporting a result")
        }
    }
}

fn solve_interruptible_bounded(
    instance: PbInstance,
    stop_budget: Duration,
    wall_budget: Duration,
) -> (PbCdclResult, PbCdclStats, Duration) {
    let (tx, rx) = mpsc::channel();

    thread::spawn(move || {
        let mut solver = PbCdclSolver::new(&instance);
        let start = Instant::now();
        let deadline = start + stop_budget;
        let result = solver.solve_interruptible(|| Instant::now() >= deadline);
        let elapsed = start.elapsed();
        let stats = solver.stats().clone();
        let _ = tx.send((result, stats, elapsed));
    });

    match rx.recv_timeout(wall_budget) {
        Ok(summary) => summary,
        Err(mpsc::RecvTimeoutError::Timeout) => {
            panic!("interruptible native PB solve exceeded {wall_budget:?} on maintenance guard")
        }
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            panic!("interruptible solver thread disconnected before reporting a result")
        }
    }
}

#[test]
fn test_preprocess_duplicate_cardinality_family_finishes_and_collapses() {
    let result = preprocess_bounded(duplicate_cardinality_instance(1024));

    let PreprocessResult::Simplified {
        instance,
        fixed_literals,
    } = result
    else {
        panic!("duplicate-heavy cardinality family should remain satisfiable");
    };

    assert!(
        fixed_literals.is_empty(),
        "exact duplicate constraints should not force literals during preprocessing"
    );
    assert_eq!(
        instance.constraints.len(),
        1,
        "exact duplicates should collapse to a single representative constraint"
    );

    let witness = vec![true, true, true, false, false, false];
    assert!(
        verify_all_constraints(&instance.constraints, &witness),
        "the simplified representative constraint must preserve the original SAT witness"
    );
}

#[test]
fn test_native_unsat_backtracking_path_finishes_with_conflicts() {
    let (result, stats) = solve_bounded(root_probe_decoy_backtracking_instance());

    assert_eq!(
        result,
        PbCdclResult::Unsatisfiable,
        "the decoy-protected pigeonhole core must remain UNSAT"
    );
    assert!(
        stats.decisions > 0,
        "the backtracking guard should still enter decision search after bounded root probing"
    );
    assert!(
        stats.conflicts > 0,
        "the backtracking guard should exercise conflict analysis"
    );
    assert!(
        stats.learned > 0,
        "the backtracking guard should learn at least one constraint"
    );
    assert!(
        stats.propagations > 0,
        "the backtracking guard should exercise propagation before concluding UNSAT"
    );
}

#[test]
fn test_interruptible_weighted_pigeonhole_finishes_and_learns_under_budget() {
    // This guard exercises the interruptible native solve path on a weighted
    // pigeonhole family: it must fail closed under interruption, respect the wall
    // budget, and learn conflict constraints. (It used to additionally assert that
    // reduce_db ran, but the RoundingSat-style asserting conflict-analysis loop
    // now closes weighted-pigeonhole proofs in O(pigeons) conflicts — e.g. P(22,21)
    // in ~21 conflicts — so the 2000-conflict reduce_db interval is never reached
    // on this family. The reduce_db maintenance path under interruption is covered
    // directly and robustly by the unit test
    // `test_solve_with_stop_interrupts_during_reduce_db_maintenance`, which forces
    // the interval rather than depending on a weak engine accumulating conflicts.)
    const STOP_BUDGET: Duration = Duration::from_secs(8);
    const WALL_BUDGET: Duration = Duration::from_secs(20);

    let (result, stats, elapsed) = solve_interruptible_bounded(
        weighted_pigeonhole_instance(22, 21),
        STOP_BUDGET,
        WALL_BUDGET,
    );

    assert!(
        matches!(result, PbCdclResult::Unknown | PbCdclResult::Unsatisfiable),
        "interruptible native solve must fail closed (Unknown) or prove UNSAT, got {result:?}"
    );
    assert!(
        elapsed <= WALL_BUDGET,
        "interruptible native solve must respect the wall budget"
    );
    assert!(
        stats.conflicts > 0,
        "weighted pigeonhole 22/21 should reach the conflict path"
    );
    assert!(
        stats.learned > 0,
        "weighted pigeonhole 22/21 should learn constraints"
    );
}
