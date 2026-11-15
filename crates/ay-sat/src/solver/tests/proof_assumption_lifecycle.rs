// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Conditional UNSAT is not an empty clause in the persistent proof formula.

use super::*;
use crate::ProofOutput;
use std::io::{self, Write};

mod support;
use support::*;

#[test]
fn drat_text_repeated_queries_do_not_poison_base() {
    repeated_queries(Format::DratText);
}

#[test]
fn drat_binary_repeated_queries_do_not_poison_base() {
    repeated_queries(Format::DratBinary);
}

#[test]
fn lrat_text_repeated_queries_do_not_poison_base() {
    repeated_queries(Format::LratText);
}

#[test]
fn lrat_binary_repeated_queries_do_not_poison_base() {
    repeated_queries(Format::LratBinary);
}

#[test]
fn drat_text_pushed_query_can_be_followed_by_sat() {
    pushed_query(Format::DratText);
}

#[test]
fn drat_binary_pushed_query_can_be_followed_by_sat() {
    pushed_query(Format::DratBinary);
}

#[test]
fn lrat_text_pushed_query_can_be_followed_by_sat() {
    pushed_query(Format::LratText);
}

#[test]
fn lrat_binary_pushed_query_can_be_followed_by_sat() {
    pushed_query(Format::LratBinary);
}

#[test]
fn drat_scoped_formula_refutation_is_retractable() {
    scoped_formula(Format::DratText);
}

#[test]
fn lrat_scoped_formula_refutation_is_retractable() {
    scoped_formula(Format::LratText);
}

#[test]
fn drat_base_refutation_still_finishes_with_empty() {
    root_refutation(Format::DratText);
}

#[test]
fn lrat_base_refutation_still_finishes_with_empty() {
    root_refutation(Format::LratText);
}

#[test]
fn drat_base_refutation_after_conditional_query_still_checks() {
    later_base_refutation(Format::DratText);
}

#[test]
fn lrat_base_refutation_after_conditional_query_still_checks() {
    later_base_refutation(Format::LratText);
}

fn unit_conflict(format: Format) {
    let original = vec![vec![p(0)]];
    let mut solver = solver(format, &original);
    let result = solver.solve_with_assumptions(&[n(0)]);
    assert_query_refutation_is_not_base(&solver, &result);
    assert!(solver.solve_with_assumptions(&[p(0)]).is_sat());
    assert!(solver.solve().is_sat());
    assert_valid_prefix(format, &original, &proof_bytes(&mut solver));
}

#[test]
fn drat_root_unit_assumption_conflict_is_conditional() {
    unit_conflict(Format::DratText);
}

#[test]
fn lrat_root_unit_assumption_conflict_is_conditional() {
    unit_conflict(Format::LratText);
}

fn learned_prefix(format: Format) {
    // F implies x, but F itself is SAT. Refuting !x requires a conflict and
    // learning, not only finalizing an already-existing original unit.
    let original = vec![vec![p(0), p(1)], vec![p(0), n(1)]];
    let mut solver = solver(format, &original);
    let result = solver.solve_with_assumptions(&[n(0)]);
    assert_query_refutation_is_not_base(&solver, &result);
    assert!(solver.num_conflicts() > 0);
    assert!(solver.solve().is_sat());
    assert_valid_prefix(format, &original, &proof_bytes(&mut solver));
}

#[test]
fn drat_assumption_search_steps_remain_valid_base_prefix() {
    learned_prefix(Format::DratText);
}

#[test]
fn lrat_assumption_search_steps_remain_valid_base_prefix() {
    learned_prefix(Format::LratText);
}

fn empty_constraint(format: Format) {
    let original = vec![vec![p(0), p(1)]];
    let mut solver = solver(format, &original);
    solver.constrain(&[]);
    let result = solver.solve_with_assumptions(&[]);
    assert_query_refutation_is_not_base(&solver, &result);
    assert!(result.unsat_core().is_some_and(|core| core.is_empty()));
    assert!(solver.solve().is_sat());
    assert_valid_prefix(format, &original, &proof_bytes(&mut solver));
}

#[test]
fn drat_empty_temporary_constraint_is_not_base_unsat() {
    empty_constraint(Format::DratText);
}

#[test]
fn lrat_empty_temporary_constraint_is_not_base_unsat() {
    empty_constraint(Format::LratText);
}

fn failed_constraint(format: Format) {
    let original = vec![vec![p(0)]];
    let mut solver = solver(format, &original);
    solver.constrain(&[n(0)]);
    let result = solver.solve_with_assumptions_interruptible(&[], || false);
    assert_query_refutation_is_not_base(&solver, &result);
    assert!(solver.solve().is_sat());
    assert_valid_prefix(format, &original, &proof_bytes(&mut solver));
}

#[test]
fn drat_failed_nonempty_constraint_is_not_base_unsat() {
    failed_constraint(Format::DratText);
}

#[test]
fn lrat_failed_nonempty_constraint_is_not_base_unsat() {
    failed_constraint(Format::LratText);
}

struct FlushFailure;

impl Write for FlushFailure {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        Ok(bytes.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Err(io::Error::new(
            io::ErrorKind::WriteZero,
            "injected flush failure",
        ))
    }
}

fn conditional_flush_failure(output: ProofOutput) {
    let mut solver = Solver::with_proof_output(2, output);
    solver.disable_all_inprocessing();
    solver.set_preprocess_enabled(false);
    solver.add_clause(vec![p(0), p(1)]);
    let result = solver.solve_with_assumptions(&[n(0), n(1)]);
    assert!(result.is_unknown());
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::ProofWriteFailure)
    );
    assert!(solver
        .last_unknown_detail()
        .is_some_and(|detail| { detail.contains("injected flush failure") }));
    assert!(!solver.has_empty_clause);
    assert!(!solver.cold.empty_clause_in_proof);
    assert!(solver.solve().is_sat());
}

#[test]
fn drat_conditional_unsat_flush_failure_is_unknown_without_base_poison() {
    conditional_flush_failure(ProofOutput::drat_text(FlushFailure));
}

#[test]
fn lrat_conditional_unsat_flush_failure_is_unknown_without_base_poison() {
    conditional_flush_failure(ProofOutput::lrat_text(FlushFailure, 1));
}

#[test]
fn lrat_conditional_unsat_preserves_authority_fail_closed() {
    let mut solver = solver(Format::LratText, &[vec![p(0), p(1)]]);
    solver
        .proof_manager
        .as_mut()
        .expect("attached manager")
        .mark_lrat_authority_fail_closed();
    let result = solver.solve_with_assumptions(&[n(0), n(1)]);
    assert!(result.is_unknown());
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::ProofFinalizationFailure)
    );
    assert!(!solver.has_empty_clause);
    assert!(!solver.cold.empty_clause_in_proof);
}

#[test]
fn existing_base_empty_takes_precedence_over_nonempty_core() {
    let original = vec![vec![p(0)], vec![n(0)]];
    let mut solver = solver(Format::DratText, &original);
    // Contradictory units are not a recorded base refutation until solving.
    assert!(solver.solve().is_unsat());
    assert!(solver.has_empty_clause);
    let result = solver.declare_unsat_assume(vec![p(1)]);
    assert!(result.is_unsat());
    assert!(solver.has_empty_clause);
    assert_valid_refutation(Format::DratText, &original, &proof_bytes(&mut solver));
}

#[test]
fn trace_only_conditional_query_keeps_query_marker_without_base_poison() {
    let mut solver = Solver::new(2);
    solver.enable_clause_trace();
    solver.disable_all_inprocessing();
    solver.set_preprocess_enabled(false);
    solver.add_clause(vec![p(0), p(1)]);
    let result = solver.solve_with_assumptions(&[n(0), n(1)]);
    assert_query_refutation_is_not_base(&solver, &result);
    assert!(solver
        .live_clause_trace()
        .is_some_and(ClauseTrace::has_empty_clause));
    assert!(solver.solve().is_sat());
}

#[test]
fn original_lrat_certificate_fixture_is_only_a_conditional_refutation() {
    // Preserve the exact historical formula and query, not the old unsound
    // unconditional-certificate expectation: x0 AND x1, assuming !x0.
    let proof = ProofOutput::lrat_text(Vec::new(), 2);
    let mut solver = Solver::with_proof_output(3, proof);
    let v0 = Variable::new(0);
    let v1 = Variable::new(1);
    solver.add_clause(vec![Literal::positive(v0)]);
    solver.add_clause(vec![Literal::positive(v1)]);
    let result = solver.solve_with_assumptions(&[Literal::negative(v0)]);
    assert_query_refutation_is_not_base(&solver, &result);
    let core = result.unsat_core().expect("conditional UNSAT core");
    assert_eq!(core, &[Literal::negative(v0)]);
    let original = vec![vec![Literal::positive(v0)], vec![Literal::positive(v1)]];
    assert_valid_prefix(Format::LratText, &original, &proof_bytes(&mut solver));
    assert!(solver
        .solve_with_assumptions(&[Literal::positive(v0)])
        .is_sat());
    assert!(solver.solve().is_sat());
}

mod caller_stop;
