// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Semantic-payload dispatch for strict proof steps.
//!
//! Inference steps share the validation's term-cost memo and progress
//! envelope; structural steps contribute no recursive term-DAG payload.

use super::step_semantic_charge::is_clause_identity_route;
use super::{
    literal_decode_payload, meter_step_term_payload, AletheRule, PayloadStats, ProofCheckError,
    ProofStep, TermCostMemo, TermId, TermStore,
};

pub(super) fn meter(
    step: &ProofStep,
    terms: &TermStore,
    derived_clauses: &[Option<Vec<TermId>>],
    memo: &mut TermCostMemo,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<PayloadStats, ProofCheckError> {
    if let Some(payload) =
        super::euf_frontier_payload::meter(step, terms, derived_clauses, progress)?
    {
        return Ok(payload);
    }
    // The resolution family and the clause-identity family never read inside
    // an atom, so their payload is the literal decode they will actually
    // perform, not a reachable-DAG walk (#literal-decode-payload, see
    // `literal_decode_payload`).
    if is_clause_identity_route(step) {
        return literal_decode_payload(step, terms, derived_clauses, progress);
    }
    match step {
        ProofStep::Resolution { .. }
        | ProofStep::Step {
            rule: AletheRule::Resolution | AletheRule::ThResolution,
            ..
        } => literal_decode_payload(step, terms, derived_clauses, progress),
        ProofStep::TheoryLemma { .. }
        | ProofStep::FiniteFieldLinear { .. }
        | ProofStep::NraSos { .. }
        | ProofStep::Step { .. } => {
            meter_step_term_payload(step, terms, derived_clauses, memo, progress)
        }
        _ => Ok(PayloadStats::default()),
    }
}
