// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn open_epoch(executor: &mut Executor, request_output: bool) {
    executor.set_produce_proofs(request_output);
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[]);
    // Private storage fixture only: no solver ran and this empty artifact is
    // not a valid refutation. These tests exercise source access, not export
    // or publication, whose independent strict checks remain mandatory.
    executor.last_result = Some(SolveResult::unsat());
    executor.last_proof = Some(Proof::new());
}

pub(super) fn fixture() -> Executor {
    let mut executor = Executor::new();
    let p = executor.ctx.terms.mk_var("exact_scope_p", CoreSort::Bool);
    let q = executor.ctx.terms.mk_var("exact_scope_q", CoreSort::Bool);
    let rebuilt = executor
        .ctx
        .terms
        .mk_var("exact_scope_rebuilt", CoreSort::Bool);
    let assumption = executor
        .ctx
        .terms
        .mk_var("exact_scope_assumption", CoreSort::Bool);
    let freshness = executor
        .ctx
        .terms
        .mk_var("exact_scope_freshness", CoreSort::Bool);
    let _unused = executor.ctx.terms.mk_var("not_a_source", CoreSort::Bool);
    executor.ctx.assertions = vec![p, q, p];
    open_epoch(&mut executor, true);
    // Populate each legacy provenance channel separately; this does not mint
    // proof authority outside this private source-parity fixture.
    executor
        .proof_problem_assertion_provenance
        .as_mut()
        .unwrap()
        .problem_assertions = vec![q, q, executor.ctx.terms.false_term()];
    executor.last_proof_rebuild_originals = vec![rebuilt, q];
    executor.last_assumptions = Some(vec![assumption, rebuilt]);
    executor.self_check_authored_assertions =
        Some(vec![freshness, executor.ctx.terms.false_term(), rebuilt]);
    executor
}

pub(super) fn run(
    executor: &Executor,
    progress: Progress<'_>,
) -> Result<Option<(Vec<TermId>, Vec<TermId>)>, ProofCheckError> {
    let Some(view) = executor.exact_plain_query_proof_source_with_resource_control(
        &executor.ctx.assertions,
        &executor.ctx.source_context_stamp(),
        progress,
    )?
    else {
        return Ok(None);
    };
    let source = view.source_closure_with_resource_control(progress)?;
    let complete = view.complete_problem_with_resource_control(progress)?;
    Ok(Some((source, complete)))
}
