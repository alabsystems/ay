// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Mapped-support screen (`reject_unmappable_refutation`) regressions.

use ay_core::Sort;

use super::*;

#[path = "mapped_support/resource_tests.rs"]
mod resource_tests;

/// A solver-stamped scoped trace over `clauses`, where SAT variable 0 names
/// the authored `p` and every other variable is internal: no SMT term names
/// it, like a bit-blast bit. `authored_not_p` also authors `(not p)`, so a
/// refutation over variable 0 alone has exact premise authority.
fn screened_executor(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    authored_not_p: bool,
) -> (Executor, TermId) {
    let mut executor = Executor::new();
    let proposition = executor.ctx.terms.mk_var("screened_p", Sort::Bool);
    let mut roots = vec![proposition];
    if authored_not_p {
        roots.push(executor.ctx.terms.mk_not_raw(proposition));
    }
    executor.ctx.assertions = roots.clone();
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[]);
    executor.proof_problem_assertion_provenance = Some(
        crate::executor::theories::solve_harness::ProofProblemAssertionProvenance {
            original_problem_assertions: roots.clone(),
            problem_assertions: roots,
            assertion_sources: Default::default(),
        },
    );

    let mut sat = ay_sat::Solver::new(num_vars);
    sat.enable_clause_trace();
    sat.push();
    for clause in clauses {
        sat.add_clause(clause.clone());
    }
    assert!(sat.solve().into_inner().is_unsat());
    let trace = sat
        .snapshot_clause_trace()
        .expect("proof-enabled scoped solver retains a trace");
    let mut var_to_term = HashMap::default();
    var_to_term.insert(0, proposition);
    executor.last_clause_trace = Some(trace);
    executor.last_var_to_term = Some(var_to_term);
    executor.last_clausification_proofs = None;
    executor.last_original_clause_theory_proofs = None;
    (executor, proposition)
}

/// The eager bit-blast shape: the contradiction lives entirely on an internal
/// variable, and the originals over named atoms are satisfiable. The fragment
/// builder can never translate such a cone, so the sidecar must decline at the
/// screen, before any trace conversion or replay.
#[test]
fn unmappable_refutation_declines_before_trace_conversion() {
    let x0 = Literal::positive(Variable::new(0));
    let x1 = Literal::positive(Variable::new(1));
    let (mut executor, proposition) =
        screened_executor(2, &[vec![x0], vec![x1], vec![x1.negated()]], false);

    // The ordinary builder agrees on the outcome: the internal variable has
    // no translation, so every original that mentions it is untranslatable.
    let trace = executor.last_clause_trace.clone().expect("installed trace");
    let mut map = HashMap::default();
    map.insert(0, proposition);
    let mut manager = SatProofManager::new(&map, &mut executor.ctx.terms);
    manager
        .set_scope_assumptions(trace.scope_assumptions().expect("solver-stamped trace"))
        .expect("the solver mints negative, ordered scope selectors");
    let exhaustive = manager.build_exact_original_proof_fragment(&trace, &[proposition]);
    assert!(
        matches!(
            exhaustive,
            Err(ExactOriginalProofError::UnmappedVariable { variable: 1, .. })
        ),
        "the fragment builder must reject the internal variable: {exhaustive:?}"
    );

    let error = CheckedSatRefutation::build(&mut executor)
        .expect_err("no refutation of this trace can be translated to SMT terms");
    assert!(
        matches!(
            error,
            CheckedSatRefutationError::UnmappableRefutation { variable: 1, .. }
        ),
        "the screen, not the post-replay fragment build, must decline: {error:?}"
    );
    executor.refresh_checked_sat_refutation();
    assert!(executor.last_checked_sat_refutation.is_none());
}

/// Counterfactual for an over-eager screen: an untranslatable original that
/// the refutation does not need must not block a refutation over named atoms.
/// The mapped originals `p` and `(not p)` are unsatisfiable on their own, so
/// the screen stays silent and the sidecar mints exactly as before.
#[test]
fn unmappable_original_outside_a_mapped_refutation_does_not_decline() {
    let x0 = Literal::positive(Variable::new(0));
    let x1 = Literal::positive(Variable::new(1));
    let (mut executor, _) =
        screened_executor(2, &[vec![x1, x0], vec![x0], vec![x0.negated()]], true);
    executor.refresh_checked_sat_refutation();
    assert!(
        executor.last_checked_sat_refutation.is_some(),
        "a refutation whose cone is all mapped must still mint"
    );
}
