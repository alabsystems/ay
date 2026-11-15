// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! [`solve_resolution_dag_counted`] and
//! [`prove_unsat_resolution_dag_counted_work`]: the bounded, cancellable
//! resolution solve that also reports the conflicts it spent.
//!
//! A caller that runs MANY small solves under one counted envelope — AY's SAT
//! sweep, thousands of local lemma refutations inside the strict checker's
//! conflict budget — must charge each solve what it spent. Charged its cap
//! instead, a solve that needs three conflicts costs its whole allowance, and
//! the envelope runs out on allowances rather than on search. A caller whose
//! second attempt shares the first one's envelope (the strict checker's
//! producer, whose sweep follows its monolithic refutation) charges it what
//! the first one spent, however the first one ended.

use crate::resolution_dag::{
    admit_controlled_outcome, solve_resolution_dag_controlled, ProofControl, ResolutionDag,
    ResolutionProofError, ResolutionProofLimits, ResolutionSolveOutcome,
};
use crate::Literal;

/// [`crate::solve_resolution_dag_with_limits_and_cancellation`], also
/// returning the conflicts the solver reported: `0` when it never searched
/// (a refusal before the search), otherwise its own count, which a solve
/// stopped by `max_conflicts` reports at or just past the cap.
pub fn solve_resolution_dag_counted(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    limits: &ResolutionProofLimits,
    keep_going: &mut dyn FnMut() -> bool,
) -> (Result<ResolutionSolveOutcome, ResolutionProofError>, u64) {
    let (result, conflicts) = solve_counted_with_work(num_vars, clauses, limits, keep_going, true);
    // This compatibility API reports search conflicts, not validation
    // work. Drop only the already-measured validation carrier; never run
    // another replay or substitute its usage for the solver's conflicts.
    (result.map(|(outcome, _validation_work)| outcome), conflicts)
}

/// [`solve_resolution_dag_counted`] for ONE OF MANY short local solves under
/// one counted envelope, the SAT sweep's lemma, split and closing
/// refutations: the same solve, but its solver does not build the parked
/// bit-parallel support enumeration (`solver/indep_enum.rs`).
///
/// That probe never claims UNSAT, and it runs only once search has had its
/// wall-clock head start: a tenth of the time left to the solve's deadline,
/// at most 30 s. A lemma solve of a few hundred conflicts ends long before
/// it; a longer split or closing solve could only have been delayed by the
/// probe's slice, or told SAT sooner, never given a refutation. So the build
/// (independent-support recovery and the XOR collapse over the whole clause
/// set) changed nothing a sweep decides but its cost: measured 2026-10-15 on
/// model-checker-consumer R30 `rem_in_range` (64-bit `x % 1000003 < 1000003`), a third of
/// a 200,000-conflict sweep, 18.7 s to 12.5 s, with the same conflicts, work
/// and outcome.
pub fn solve_resolution_dag_counted_local(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    limits: &ResolutionProofLimits,
    keep_going: &mut dyn FnMut() -> bool,
) -> (Result<ResolutionSolveOutcome, ResolutionProofError>, u64) {
    let (result, conflicts) = solve_counted_with_work(num_vars, clauses, limits, keep_going, false);
    (result.map(|(outcome, _validation_work)| outcome), conflicts)
}

/// [`crate::prove_unsat_resolution_dag_with_limits_and_cancellation_work`]
/// (the same single solve, replay, callbacks and admission), also returning
/// the conflicts the solver reported, as [`solve_resolution_dag_counted`]
/// does. The count accompanies EVERY outcome: an attempt stopped by its proof
/// output, hint or step caps still reports the search it ran.
pub fn prove_unsat_resolution_dag_counted_work(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    limits: &ResolutionProofLimits,
    keep_going: &mut dyn FnMut() -> bool,
) -> (Result<(ResolutionDag, u64), ResolutionProofError>, u64) {
    let (result, conflicts) = solve_counted_with_work(num_vars, clauses, limits, keep_going, true);
    let proved = result.and_then(|(outcome, work)| match outcome {
        ResolutionSolveOutcome::Sat(_) => Err(ResolutionProofError::Satisfiable),
        ResolutionSolveOutcome::Unsat(dag) => Ok((dag, work)),
    });
    (proved, conflicts)
}

/// One controlled solve, its admitted outcome with the producer's own
/// validation work, and the conflicts the solver recorded.
fn solve_counted_with_work(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    limits: &ResolutionProofLimits,
    keep_going: &mut dyn FnMut() -> bool,
    support_enumeration: bool,
) -> (
    Result<(ResolutionSolveOutcome, u64), ResolutionProofError>,
    u64,
) {
    let control = ProofControl::new(keep_going);
    let result = control.run(|control| {
        solve_resolution_dag_controlled(num_vars, clauses, limits, control, support_enumeration)
    });
    let conflicts = control.conflicts();
    let admitted = result.and_then(|(outcome, work)| {
        admit_controlled_outcome(Ok(outcome), limits).map(|outcome| (outcome, work))
    });
    (admitted, conflicts)
}
