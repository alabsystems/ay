// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Semantic-payload dispatch for strict proof steps.
//!
//! Inference steps share the validation's term-cost memo and progress
//! envelope; structural steps contribute no recursive term-DAG payload.

use super::{
    meter_step_term_payload, PayloadStats, ProofCheckError, ProofStep, TermCostMemo, TermId,
    TermStore,
};

pub(super) fn meter(
    step: &ProofStep,
    terms: &TermStore,
    derived_clauses: &[Option<Vec<TermId>>],
    memo: &mut TermCostMemo,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<PayloadStats, ProofCheckError> {
    match step {
        ProofStep::Resolution { .. } | ProofStep::TheoryLemma { .. } | ProofStep::Step { .. } => {
            meter_step_term_payload(step, terms, derived_clauses, memo, progress)
        }
        _ => Ok(PayloadStats::default()),
    }
}
