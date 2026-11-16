// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Same native conditions as replay::native_solve, with assertion-only context.

use super::*;
use ay_dpll::api::{Logic, Solver};

pub(super) fn accepted(
    stage: &str,
    script: &str,
    end: Instant,
    memory: Option<usize>,
    token: &CancellationToken,
    owner: &SourceControl<'_>,
) -> Solver {
    owner
        .poll()
        .unwrap_or_else(|| panic!("stage {stage}: original owner refused at entry"));
    assert_ne!(memory, Some(0), "stage {stage}: exact zero cap refuses");
    assert!(
        Instant::now() < end,
        "stage {stage}: original deadline spent at entry"
    );
    let body = script
        .strip_prefix("(set-logic ALL)\n")
        .unwrap_or_else(|| panic!("stage {stage}: exact renderer header absent"));
    let mut solver = Solver::try_new(Logic::All)
        .unwrap_or_else(|error| panic!("stage {stage}: native construction refused: {error:?}"));
    solver.set_term_memory_limit(memory);
    owner
        .poll()
        .unwrap_or_else(|| panic!("stage {stage}: original construction owner refused"));
    let assertions = solver.parse_smtlib2(body).unwrap_or_else(|error| {
        panic!("stage {stage}: native parse refused: {error:?}; script={script}")
    });
    assert!(!assertions.is_empty(), "stage {stage}: no hard assertions");
    drop(assertions);
    owner
        .poll()
        .unwrap_or_else(|| panic!("stage {stage}: original parse owner refused"));
    assert!(
        memory.is_none_or(|limit| solver.instance_term_bytes() <= limit),
        "stage {stage}: original term cap exceeded"
    );
    assert!(
        Instant::now() < end,
        "stage {stage}: original deadline spent after parse"
    );
    solver.set_timeout(Some(end.saturating_duration_since(Instant::now())));
    let attempt = token.sticky_child();
    let verdict = solver.check_sat_interruptible_internal_query(move || {
        attempt.is_cancelled()
            || Instant::now() >= end
            || ay_core::TermStore::global_memory_exceeded()
    });
    owner
        .poll()
        .unwrap_or_else(|| panic!("stage {stage}: original solve owner refused"));
    assert!(
        Instant::now() < end,
        "stage {stage}: original deadline spent after solve"
    );
    assert!(
        memory.is_none_or(|limit| solver.instance_term_bytes() <= limit),
        "stage {stage}: original term cap exceeded after solve"
    );
    assert!(
        verdict.is_sat() && verdict.was_model_validated() && verdict.has_sat_emission_witness(),
        "stage {stage}: native accepted SAT absent; sat={} model={} emission={} unknown={:?} \
         executor={:?} phase={:?} detail={:?} quantified_reason={:?}; script={script}",
        verdict.is_sat(),
        verdict.was_model_validated(),
        verdict.has_sat_emission_witness(),
        solver.unknown_reason(),
        solver.executor_error(),
        solver.statistics().get_string("unknown.phase"),
        solver.statistics().get_string("unknown.detail"),
        solver
            .statistics()
            .get_string("model_check_gate.quantified_reason")
    );
    solver
}
