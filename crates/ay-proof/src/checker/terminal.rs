// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authenticate the last clause-producing step, including trailing anchors.
//!
//! #completed-check-accepted — this is bookkeeping over steps the walk has
//! ALREADY admitted and validated, so it takes no progress callback. The
//! reverse scan reads at most one `Option` per step, and every one of those
//! steps paid its own admission charge inside the step loop. It also runs
//! after the final step, where a callback could only do one thing: turn a
//! validation that finished every step into `ResourceLimit` because a stop
//! signal arrived late. A metered variant used to do exactly that (a zero-delta
//! poll before and after the scan); it was the last of the checker's
//! post-completion polls and is gone.

use ay_core::{ProofId, TermId};

use super::ProofCheckError;

pub(crate) fn ensure_terminal_empty_clause(
    derived_clauses: &[Option<Vec<TermId>>],
) -> Result<(), ProofCheckError> {
    for (index, clause) in derived_clauses.iter().enumerate().rev() {
        let Some(clause) = clause else { continue };
        if !clause.is_empty() {
            let index = u32::try_from(index).map_err(|_| ProofCheckError::ResourceLimit)?;
            return Err(ProofCheckError::FinalClauseNotEmpty {
                step: ProofId(index),
            });
        }
        return Ok(());
    }
    Err(ProofCheckError::NoClauseProducingSteps)
}

#[cfg(test)]
mod tests {
    use super::*;

    mod integration;

    #[test]
    fn terminal_scan_preserves_last_clause_and_empty_anchor_semantics() {
        for (clauses, expected) in [
            (vec![], Err(ProofCheckError::NoClauseProducingSteps)),
            (
                vec![None, None],
                Err(ProofCheckError::NoClauseProducingSteps),
            ),
            (vec![Some(vec![])], Ok(())),
            (vec![Some(vec![]), None, None], Ok(())),
            (vec![Some(vec![TermId(0)]), Some(vec![])], Ok(())),
            (
                vec![Some(vec![]), Some(vec![TermId(0)]), None],
                Err(ProofCheckError::FinalClauseNotEmpty { step: ProofId(1) }),
            ),
        ] {
            assert_eq!(ensure_terminal_empty_clause(&clauses), expected);
        }
    }
}
