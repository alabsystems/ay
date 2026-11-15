// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::cell::Cell;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

#[derive(Clone)]
struct SinkState {
    armed: Arc<AtomicBool>,
    caller_stop: Arc<AtomicBool>,
    flushes: Arc<AtomicUsize>,
    bytes: Arc<Mutex<Vec<u8>>>,
}

impl SinkState {
    fn new() -> Self {
        Self {
            armed: Arc::new(AtomicBool::new(false)),
            caller_stop: Arc::new(AtomicBool::new(false)),
            flushes: Arc::new(AtomicUsize::new(0)),
            bytes: Arc::new(Mutex::new(Vec::new())),
        }
    }

    fn arm(&self) {
        self.armed.store(true, Ordering::Relaxed);
    }

    fn fresh_query(&self) {
        self.armed.store(false, Ordering::Relaxed);
        self.caller_stop.store(false, Ordering::Relaxed);
    }
}

#[derive(Clone, Copy)]
enum FlushAction {
    Stop,
    StopAndFail,
}

struct CallerFlush {
    state: SinkState,
    action: FlushAction,
}

impl Write for CallerFlush {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        self.state
            .bytes
            .lock()
            .expect("test sink")
            .extend_from_slice(bytes);
        Ok(bytes.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        self.state.flushes.fetch_add(1, Ordering::Relaxed);
        if self.state.armed.load(Ordering::Relaxed) {
            self.state.caller_stop.store(true, Ordering::Relaxed);
            if matches!(self.action, FlushAction::StopAndFail) {
                return Err(io::Error::new(
                    io::ErrorKind::WriteZero,
                    "caller-stop flush failure",
                ));
            }
        }
        Ok(())
    }
}

fn formats() -> [Format; 4] {
    [
        Format::DratText,
        Format::DratBinary,
        Format::LratText,
        Format::LratBinary,
    ]
}

fn with_sink(
    format: Format,
    clauses: &[Vec<Literal>],
    state: &SinkState,
    action: FlushAction,
) -> Solver {
    let sink = CallerFlush {
        state: state.clone(),
        action,
    };
    let output = match format {
        Format::DratText => ProofOutput::drat_text(sink),
        Format::DratBinary => ProofOutput::drat_binary(sink),
        Format::LratText => ProofOutput::lrat_text(sink, clauses.len() as u64),
        Format::LratBinary => ProofOutput::lrat_binary(sink, clauses.len() as u64),
    };
    let mut solver = Solver::with_proof_output(3, output);
    solver.disable_all_inprocessing();
    solver.set_preprocess_enabled(false);
    for clause in clauses {
        solver.add_clause(clause.clone());
    }
    solver
}

fn assert_caller_unknown(solver: &Solver, result: &SolverAssumeResult) {
    assert!(result.is_unknown());
    assert!(result.proof_certificate().is_none());
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::Interrupted)
    );
    assert!(
        !solver.is_interrupted(),
        "no native interrupt was installed or raised"
    );
}

#[test]
fn caller_only_conditional_flush_refusal_survives_all_four_proof_formats() {
    for format in formats() {
        let original = vec![vec![p(0), p(1)]];
        let state = SinkState::new();
        let mut solver = with_sink(format, &original, &state, FlushAction::Stop);
        let before = state.flushes.load(Ordering::Relaxed);
        state.arm();
        let result = solver.solve_with_assumptions_interruptible(&[n(0), n(1)], || {
            state.caller_stop.load(Ordering::Relaxed)
        });
        assert_caller_unknown(&solver, &result);
        assert!(state.flushes.load(Ordering::Relaxed) > before);
        assert!(!solver.has_empty_clause);
        assert!(!solver.cold.empty_clause_in_proof);
        assert_eq!(solver.cold.empty_clause_lrat_id, None);
        let bytes = state.bytes.lock().expect("test sink").clone();
        assert_valid_prefix(format, &original, &bytes);
        state.fresh_query();
        assert!(solver
            .solve_with_assumptions_interruptible(&[p(0)], || false)
            .is_sat());
    }
}

#[test]
fn caller_only_base_flush_refusal_cannot_publish_a_certificate() {
    for format in formats() {
        let original = vec![vec![p(0)], vec![n(0)]];
        let state = SinkState::new();
        let mut solver = with_sink(format, &original, &state, FlushAction::Stop);
        state.arm();
        let result = solver.solve_with_assumptions_interruptible(&[p(1)], || {
            state.caller_stop.load(Ordering::Relaxed)
        });
        assert_caller_unknown(&solver, &result);
        assert!(state.flushes.load(Ordering::Relaxed) > 0);
        assert!(
            solver.has_empty_clause,
            "the genuine semantic base contradiction stays"
        );
        let bytes = state.bytes.lock().expect("test sink").clone();
        assert_valid_refutation(format, &original, &bytes);
        state.fresh_query();
        assert!(solver
            .solve_with_assumptions_interruptible(&[p(1)], || false)
            .is_unsat());
    }
}

#[test]
fn successful_flush_stop_still_clears_and_melts_original_temporary_constraint() {
    for format in formats() {
        let original = vec![vec![p(0)]];
        let state = SinkState::new();
        let mut solver = with_sink(format, &original, &state, FlushAction::Stop);
        solver.constrain(&[n(0)]);
        assert!(solver.is_frozen(Variable::new(0)));
        state.arm();
        let result = solver.solve_with_assumptions_interruptible(&[], || {
            state.caller_stop.load(Ordering::Relaxed)
        });
        assert_caller_unknown(&solver, &result);
        assert!(solver.cold.constraint.is_empty());
        assert!(!solver.failed_constraint());
        assert!(!solver.is_frozen(Variable::new(0)));
        assert!(!solver.has_empty_clause);
        assert!(!solver.cold.empty_clause_in_proof);
        let bytes = state.bytes.lock().expect("test sink").clone();
        assert_valid_prefix(format, &original, &bytes);
        state.fresh_query();
        assert!(solver
            .solve_with_assumptions_interruptible(&[p(0)], || false)
            .is_sat());
    }
}

#[test]
fn writer_error_during_caller_stop_has_exact_original_precedence() {
    for format in formats() {
        let state = SinkState::new();
        let mut solver = with_sink(
            format,
            &[vec![p(0), p(1)]],
            &state,
            FlushAction::StopAndFail,
        );
        let late_polls = Cell::new(0);
        state.arm();
        let result = solver.solve_with_assumptions_interruptible(&[n(0), n(1)], || {
            let stopped = state.caller_stop.load(Ordering::Relaxed);
            late_polls.set(late_polls.get() + usize::from(stopped));
            stopped
        });
        assert!(result.is_unknown());
        assert_eq!(
            solver.last_unknown_reason(),
            Some(SatUnknownReason::ProofWriteFailure)
        );
        assert!(solver
            .last_unknown_detail()
            .is_some_and(|d| d.contains("caller-stop flush failure")));
        assert_eq!(
            late_polls.get(),
            0,
            "an already refused result is not reclassified"
        );
        assert!(state.caller_stop.load(Ordering::Relaxed));
        assert!(!solver.has_empty_clause);
        assert!(!solver.cold.empty_clause_in_proof);
        state.fresh_query();
        assert!(solver
            .solve_with_assumptions_interruptible(&[p(0)], || false)
            .is_sat());
    }
}

#[test]
fn authority_refusal_during_caller_stop_is_not_reclassified_as_interrupt() {
    for format in [Format::LratText, Format::LratBinary] {
        let state = SinkState::new();
        let mut solver = with_sink(format, &[vec![p(0), p(1)]], &state, FlushAction::Stop);
        solver
            .proof_manager
            .as_mut()
            .expect("attached manager")
            .mark_lrat_authority_fail_closed();
        state.arm();
        let result = solver.solve_with_assumptions_interruptible(&[n(0), n(1)], || {
            state.caller_stop.load(Ordering::Relaxed)
        });
        assert!(result.is_unknown());
        assert_eq!(
            solver.last_unknown_reason(),
            Some(SatUnknownReason::ProofFinalizationFailure)
        );
        assert!(state.caller_stop.load(Ordering::Relaxed));
        assert!(!solver.has_empty_clause);
        assert!(!solver.cold.empty_clause_in_proof);
    }
}

#[test]
fn empty_constraint_final_callback_stops_after_original_cleanup() {
    let mut solver = Solver::new(3);
    solver.disable_all_inprocessing();
    solver.set_preprocess_enabled(false);
    solver.add_clause(vec![p(0), p(1)]);
    solver.constrain(&[]);
    let polls = Cell::new(0);
    let result = solver.solve_with_assumptions_interruptible(&[], || {
        let count = polls.get() + 1;
        polls.set(count);
        count == 2
    });
    assert_caller_unknown(&solver, &result);
    assert_eq!(
        polls.get(),
        2,
        "entry, then final admission after early raw cleanup"
    );
    assert!(solver.cold.constraint.is_empty());
    assert!(!solver.failed_constraint());
    assert!(!solver.has_empty_clause);
    assert!(solver
        .solve_with_assumptions_interruptible(&[], || false)
        .is_sat());
}

#[test]
fn observed_entry_refusal_is_not_repolled_or_carried_into_a_fresh_attempt() {
    let mut solver = Solver::new(3);
    solver.add_clause(vec![p(0), p(1)]);
    solver.constrain(&[p(0)]);
    let polls = Cell::new(0);
    let stop_once = || {
        let count = polls.get() + 1;
        polls.set(count);
        count == 1
    };
    let refused = solver.solve_with_assumptions_interruptible(&[], &stop_once);
    assert_caller_unknown(&solver, &refused);
    assert_eq!(polls.get(), 1);
    assert!(solver.cold.constraint.is_empty());
    assert!(!solver.is_frozen(Variable::new(0)));
    assert!(solver
        .solve_with_assumptions_interruptible(&[], &stop_once)
        .is_sat());
}

#[test]
fn late_gate_retires_owned_recording_without_duplicate_terminal_or_replay_bypass() {
    let directory = tempfile::tempdir().expect("test trace directory");
    let path = directory.path().join("raw.decision");
    let path = path.to_str().expect("test trace path");
    let state = SinkState::new();
    let mut solver = with_sink(
        Format::DratText,
        &[vec![p(0), p(1)]],
        &state,
        FlushAction::Stop,
    );
    solver
        .enable_decision_trace(path)
        .expect("original raw trace");
    state.arm();
    let result = solver.solve_with_assumptions_interruptible(&[n(0), n(1)], || {
        state.caller_stop.load(Ordering::Relaxed)
    });
    assert_caller_unknown(&solver, &result);
    assert_eq!(std::fs::metadata(path).expect("retained trace").len(), 0);
    assert!(crate::decision_trace::read_trace(path).is_err());
    assert!(
        !solver.disable_decision_trace(),
        "the rejected writer was already detached"
    );
    assert!(solver.cold.replay_trace.is_none());
}

#[test]
fn final_caller_refusal_invalidates_only_the_original_trace_inode() {
    let directory = tempfile::tempdir().expect("test trace directory");
    let path = directory.path().join("raw.decision");
    let moved = directory.path().join("owned-inode.decision");
    let path_text = path.to_str().expect("test trace path");
    let state = SinkState::new();
    let mut solver = with_sink(
        Format::DratText,
        &[vec![p(0), p(1)]],
        &state,
        FlushAction::Stop,
    );
    solver
        .enable_decision_trace(path_text)
        .expect("original raw trace");
    state.arm();
    let swapped = Cell::new(false);
    let result = solver.solve_with_assumptions_interruptible(&[n(0), n(1)], || {
        if state.caller_stop.load(Ordering::Relaxed) {
            assert!(
                !swapped.replace(true),
                "one original final callback observation"
            );
            std::fs::rename(&path, &moved).expect("move original inode");
            std::fs::write(&path, b"foreign replacement untouched").expect("foreign inode");
            true
        } else {
            false
        }
    });
    assert_caller_unknown(&solver, &result);
    assert!(swapped.get());
    assert_eq!(std::fs::metadata(moved).expect("owned inode").len(), 0);
    assert_eq!(
        std::fs::read(path).expect("foreign inode"),
        b"foreign replacement untouched"
    );
    assert!(!solver.disable_decision_trace());
}
