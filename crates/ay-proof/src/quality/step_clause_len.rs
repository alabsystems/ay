// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn step_clause_len(step: &ProofStep) -> usize {
    match step {
        ProofStep::Assume(_) => 1,
        ProofStep::Resolution { clause, .. }
        | ProofStep::TheoryLemma { clause, .. }
        | ProofStep::Step { clause, .. } => clause.len(),
        ProofStep::Anchor { .. } => 0,
        _ => 0,
    }
}
