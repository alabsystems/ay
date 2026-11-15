// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A proof write that fails for lack of space never panics. On 2026-09-12 a
//! full disk on m100 panicked `ay solve` at the inprocessing boundary assert
//! (exit 101, no verdict line) while it wrote a VeriPB proof for SAT-COMP
//! `0d0fabe0`. Since 2026-09-19 (owner) the search goes on after the writer
//! latched: a SAT is answered with its model, and an UNSAT, which the lost
//! proof cannot certify, is answered unknown with
//! [`SatUnknownReason::ProofWriteFailure`] and a detail naming the OS error.

use super::*;
use crate::ProofOutput;
use std::io::{self, Write};

/// A proof sink that accepts `budget` bytes and then reports a full disk.
#[cfg(unix)]
struct NoSpaceAfter {
    written: usize,
    budget: usize,
}

#[cfg(unix)]
impl Write for NoSpaceAfter {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        if self.written + buf.len() > self.budget {
            return Err(io::Error::from_raw_os_error(libc::ENOSPC));
        }
        self.written += buf.len();
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[cfg(unix)]
fn full_after(budget: usize) -> NoSpaceAfter {
    NoSpaceAfter { written: 0, budget }
}

/// Pigeonhole PHP(pigeons, holes): UNSAT for pigeons > holes, and hard enough
/// that search writes many proof steps.
fn add_pigeonhole(solver: &mut Solver, pigeons: u32, holes: u32) {
    let var = |p: u32, h: u32| Variable(p * holes + h);
    for p in 0..pigeons {
        solver.add_clause((0..holes).map(|h| Literal::positive(var(p, h))).collect());
    }
    for h in 0..holes {
        for p in 0..pigeons {
            for q in (p + 1)..pigeons {
                solver.add_clause(vec![
                    Literal::negative(var(p, h)),
                    Literal::negative(var(q, h)),
                ]);
            }
        }
    }
}

/// The disk fills during search and the formula is UNSAT: the solve answers
/// unknown with `ProofWriteFailure` and names the OS error, on the shipped
/// VeriPB surface and on DRAT.
#[cfg(unix)]
#[test]
fn test_enospc_during_search_answers_unknown_for_unsat_and_names_the_cause() {
    let (pigeons, holes) = (8, 7);
    for (name, output) in [
        ("veripb", ProofOutput::veripb(full_after(4096))),
        ("drat_text", ProofOutput::drat_text(full_after(4096))),
    ] {
        let mut solver: Solver = Solver::with_proof_output((pigeons * holes) as usize, output);
        add_pigeonhole(&mut solver, pigeons, holes);
        let result = solver.solve().into_inner();
        assert!(
            result.is_unknown(),
            "{name}: a lost proof cannot certify UNSAT"
        );
        assert_eq!(
            solver.last_unknown_reason(),
            Some(SatUnknownReason::ProofWriteFailure),
            "{name}"
        );
        let detail = solver.last_unknown_detail().unwrap_or_default();
        assert!(
            detail.starts_with("proof write failed: ")
                && detail.contains("No space left on device"),
            "{name}: {detail}"
        );
    }
}

/// The disk fills during search and the formula is SAT: the search goes on
/// after the latch and answers with a verified model, which needs no proof.
#[cfg(unix)]
#[test]
fn test_enospc_during_search_still_answers_sat_with_its_model() {
    let (pigeons, holes) = (7, 7);
    for (name, output) in [
        ("veripb", ProofOutput::veripb(full_after(4096))),
        ("drat_text", ProofOutput::drat_text(full_after(4096))),
    ] {
        let mut solver: Solver = Solver::with_proof_output((pigeons * holes) as usize, output);
        add_pigeonhole(&mut solver, pigeons, holes);
        let result = solver.solve().into_inner();
        assert!(
            solver.proof_writer().is_some_and(ProofOutput::has_io_error),
            "{name}: the search must have written past the budget"
        );
        assert!(
            result.is_sat(),
            "{name}: SAT needs no proof; got {result:?}"
        );
        assert!(
            solver
                .proof_write_failure()
                .is_some_and(|detail| detail.contains("No space left on device")),
            "{name}"
        );
    }
}

/// The exact crash site: an inprocessing round that runs after the writer
/// latched must finish without tripping the boundary assert.
#[cfg(unix)]
#[test]
fn test_inprocessing_boundary_tolerates_a_full_disk() {
    let mut solver: Solver = Solver::with_proof_output(3, ProofOutput::veripb(full_after(0)));
    let x0 = Literal::positive(Variable(0));
    // x0 is a backbone literal, so the binary backbone derives and writes a unit.
    solver.add_clause_db(&[x0, Literal::positive(Variable(1))], false);
    solver.add_clause_db(&[x0, Literal::negative(Variable(1))], false);
    solver.initialize_watches();
    solver.disable_all_inprocessing();
    solver.set_backbone_enabled(true);
    solver.cold.next_inprobe_conflict = 0;
    solver.inproc_ctrl.backbone.next_conflict = 0;
    solver.num_conflicts = BACKBONE_INTERVAL;
    assert!(
        !solver.proof_output_failed(),
        "no write has hit the disk yet"
    );
    assert_eq!(solver.solve_stop_reason(&|| false), None);
    assert!(
        !solver.run_restart_inprocessing(),
        "the round must complete without panicking"
    );
    assert!(
        solver.proof_writer().is_some_and(ProofOutput::has_io_error),
        "the unit write must have hit the full disk"
    );
    assert!(solver.proof_output_failed());
    // The full disk is no stop: the poll answers only a real stop, and the
    // next inprocessing round runs on the muted writer without panicking.
    assert_eq!(solver.solve_stop_reason(&|| false), None);
    assert_eq!(
        solver.solve_stop_reason(&|| true),
        Some(SatUnknownReason::Interrupted)
    );
    solver.cold.next_inprobe_conflict = 0;
    solver.inproc_ctrl.backbone.next_conflict = 0;
    let _ = solver.run_restart_inprocessing();
}
