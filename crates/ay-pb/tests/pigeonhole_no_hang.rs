// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Wall-clock regression guard for #8724: PB CDCL with VeriPB proof logging
//! MUST NOT hang on pigeonhole-principle UNSAT instances.
//!
//! The bug:
//! - Round-to-one conflict analysis (#8681) and VeriPB proof logging (#8683)
//!   each passed independently, but their combination caused infinite looping
//!   on pigeonhole 3/2 (6 vars, 5 constraints).
//! - Root cause: cutting-planes resolution can produce constraints containing
//!   both `x` and `~x` with positive coefficients. `CpConstraint::normalize`
//!   did not apply the `x + ~x = 1` identity, so the learned constraint was
//!   tautologically weak and could not propagate after backtrack. VSIDS
//!   repeated the same decision, the same conflict reproduced, and the solver
//!   looped indefinitely.
//! - Fix: `CpConstraint::normalize` now calls `cancel_complementary_literals`
//!   (commit 21b485b0f).
//!
//! This test exists to catch any regression that re-introduces the hang.
//! It enforces a strict wall-clock bound by running the solver on a background
//! thread and asserting it reports UNSAT within the budget.

use std::sync::mpsc;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

use ay_pb::{PbCdclResult, PbCdclSolver, PbConstraint, PbInstance, PbLit, PbRel, PbTerm};

/// Wall-clock bound for the hang-guard test. If the solver has not reported a
/// result in this time, the test fails. Pigeonhole 3/2 is solved by the
/// current `PbCdclSolver` in well under 1 ms, so 5 s is ample headroom for
/// slow CI machines while still catching any reintroduction of the hang.
const SOLVE_BUDGET: Duration = Duration::from_secs(5);

/// A thread-safe `std::io::Write` sink that captures bytes into a shared
/// buffer. Used as the VeriPB proof writer so the test thread owns the buffer
/// but the solver thread writes into it.
#[derive(Clone)]
struct SharedBytes(Arc<Mutex<Vec<u8>>>);

impl SharedBytes {
    fn new() -> Self {
        Self(Arc::new(Mutex::new(Vec::new())))
    }
}

impl std::io::Write for SharedBytes {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.0
            .lock()
            .expect("proof writer mutex must not be poisoned")
            .extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

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

/// Pigeonhole 3/2: 3 pigeons, 2 holes. Unsatisfiable by pigeon-principle.
///
/// Variables: `x1..x6` where `x(2p-1)` = "pigeon p in hole 1", `x(2p)` =
/// "pigeon p in hole 2".
///
/// Constraints:
/// - Each pigeon is in at least one hole: `x1+x2>=1`, `x3+x4>=1`, `x5+x6>=1`.
/// - Each hole holds at most one pigeon (written as >= on negated lits):
///   `~x1+~x3+~x5 >= 2`, `~x2+~x4+~x6 >= 2`.
fn pigeonhole_3_2() -> PbInstance {
    PbInstance {
        num_vars: 6,
        num_constraints: 5,
        constraints: vec![
            ge_constraint(vec![linear_term(1, lit(1)), linear_term(1, lit(2))], 1),
            ge_constraint(vec![linear_term(1, lit(3)), linear_term(1, lit(4))], 1),
            ge_constraint(vec![linear_term(1, lit(5)), linear_term(1, lit(6))], 1),
            ge_constraint(
                vec![
                    linear_term(1, not(1)),
                    linear_term(1, not(3)),
                    linear_term(1, not(5)),
                ],
                2,
            ),
            ge_constraint(
                vec![
                    linear_term(1, not(2)),
                    linear_term(1, not(4)),
                    linear_term(1, not(6)),
                ],
                2,
            ),
        ],
        objective: None,
    }
}

/// Solves `instance` with VeriPB proof logging on a background thread,
/// enforcing `SOLVE_BUDGET` as a strict wall-clock bound.
///
/// Returns `(result, proof_bytes)` on success. Panics if the budget is
/// exceeded — that is the hang signal #8724 is guarding against. The solver
/// thread is detached rather than joined on timeout because there is no safe
/// way to interrupt a hanging thread from the outside in stable Rust; the
/// test harness process will be torn down by the enclosing
/// `cargo test`/CI timeout if the detached thread is still running.
fn solve_with_proof_bounded(instance: PbInstance) -> (PbCdclResult, Vec<u8>) {
    let buf = SharedBytes::new();
    let buf_for_thread = buf.clone();
    let (tx, rx) = mpsc::channel();

    thread::spawn(move || {
        let mut solver = match PbCdclSolver::with_proof_writer(&instance, buf_for_thread) {
            Ok(s) => s,
            Err(e) => {
                let _ = tx.send(Err(format!("proof writer creation failed: {e:?}")));
                return;
            }
        };
        let result = solver.solve();
        if let Err(e) = solver.conclude_proof() {
            let _ = tx.send(Err(format!("proof conclusion failed: {e:?}")));
            return;
        }
        let _ = tx.send(Ok(result));
    });

    match rx.recv_timeout(SOLVE_BUDGET) {
        Ok(Ok(result)) => {
            let bytes = buf
                .0
                .lock()
                .expect("proof buffer mutex must not be poisoned")
                .clone();
            (result, bytes)
        }
        Ok(Err(msg)) => panic!("solver thread returned error: {msg}"),
        Err(mpsc::RecvTimeoutError::Timeout) => panic!(
            "PB CDCL + VeriPB proof logging hung on pigeonhole 3/2 UNSAT \
             (>{SOLVE_BUDGET:?}): regression of #8724",
        ),
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            panic!("solver thread disconnected before reporting a result")
        }
    }
}

/// The primary hang-guard: pigeonhole 3/2 UNSAT must terminate within
/// `SOLVE_BUDGET` with proof logging enabled.
#[test]
fn test_proof_logging_pigeonhole_3_2_does_not_hang() {
    let (result, proof_bytes) = solve_with_proof_bounded(pigeonhole_3_2());
    assert_eq!(
        result,
        PbCdclResult::Unsatisfiable,
        "pigeonhole 3/2 must be UNSAT"
    );

    let proof = String::from_utf8(proof_bytes).expect("proof output must be valid UTF-8");
    assert!(
        proof.starts_with("pseudo-Boolean proof version"),
        "proof must start with VeriPB header, got: {proof}"
    );
    assert!(
        proof
            .lines()
            .any(|line| line.starts_with("conclusion UNSAT : ")),
        "UNSAT proof must conclude with a VeriPB UNSAT footer: {proof}"
    );
    assert!(
        proof.lines().last() == Some("end pseudo-Boolean proof;"),
        "UNSAT proof must end with the VeriPB proof terminator: {proof}"
    );
}

/// Same UNSAT instance without proof logging — establishes a baseline that the
/// hang is specific to the proof-logging path. If this test ever hangs too,
/// the regression is deeper than #8724.
#[test]
fn test_pigeonhole_3_2_baseline_without_proof_does_not_hang() {
    let (tx, rx) = mpsc::channel();
    let instance = pigeonhole_3_2();
    thread::spawn(move || {
        let mut solver = PbCdclSolver::new(&instance);
        let _ = tx.send(solver.solve());
    });

    match rx.recv_timeout(SOLVE_BUDGET) {
        Ok(result) => assert_eq!(
            result,
            PbCdclResult::Unsatisfiable,
            "pigeonhole 3/2 must be UNSAT without proof logging"
        ),
        Err(mpsc::RecvTimeoutError::Timeout) => panic!(
            "PB CDCL (no proof logging) hung on pigeonhole 3/2 UNSAT \
             (>{SOLVE_BUDGET:?}): regression in baseline solver, not #8724",
        ),
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            panic!("solver thread disconnected before reporting a result")
        }
    }
}
