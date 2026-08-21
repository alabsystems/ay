// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Reject any authored leaf in the dependency cone of an empty clause unless
/// it is an actual problem-scope assertion. This is the production authority
/// boundary: an internally well-formed proof is still invalid if preprocessing
/// quietly introduced a stronger `Assume`.
pub fn validate_reachable_assumes_in_problem_scope(
    proof: &Proof,
    problem_assertions: &[TermId],
) -> Result<(), AlethePrintError> {
    let problem_assertions: HashSet<TermId> = problem_assertions.iter().copied().collect();
    let mut reachable = vec![false; proof.steps.len()];
    let mut stack = Vec::new();
    for (index, step) in proof.steps.iter().enumerate() {
        let derives_empty = match step {
            ProofStep::Step { clause, .. }
            | ProofStep::Resolution { clause, .. }
            | ProofStep::TheoryLemma { clause, .. } => clause.is_empty(),
            ProofStep::Assume(_) | ProofStep::Anchor { .. } => false,
            _ => false,
        };
        if derives_empty {
            reachable[index] = true;
            stack.push(index);
        }
    }
    while let Some(index) = stack.pop() {
        let mut push = |premise: ProofId| {
            let premise = premise.0 as usize;
            if premise < reachable.len() && !reachable[premise] {
                reachable[premise] = true;
                stack.push(premise);
            }
        };
        match &proof.steps[index] {
            ProofStep::Step { premises, .. } => {
                for &premise in premises {
                    push(premise);
                }
            }
            ProofStep::Resolution {
                clause1, clause2, ..
            } => {
                push(*clause1);
                push(*clause2);
            }
            _ => {}
        }
    }
    for (index, step) in proof.steps.iter().enumerate() {
        if !reachable[index] {
            continue;
        }
        if let ProofStep::Assume(term) = step {
            if !problem_assertions.contains(term) {
                return Err(AlethePrintError::NonProblemAssume {
                    id: ProofId(index as u32),
                    term: *term,
                });
            }
        }
    }
    Ok(())
}
