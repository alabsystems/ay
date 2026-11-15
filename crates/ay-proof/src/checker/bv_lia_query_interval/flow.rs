// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared metered interval propagation for authored facts and isolated cases.

use super::*;

impl QueryChecker<'_> {
    /// Same source-clause propagation for the baseline and each isolated case.
    pub(super) fn propagate_interval_clauses(
        &mut self,
        clauses: &[Vec<ClauseLiteral>],
        state: &mut IntervalState,
        entry_work: u64,
    ) -> Result<AssumeOutcome, BvLiaUnsatAuthenticationError> {
        for _ in 0..MAX_INTERVAL_ROUNDS {
            let mut changed = false;
            for clause in clauses {
                self.meter.charge(1)?;
                if self.meter.work.saturating_sub(entry_work) > MAX_INTERVAL_WORK {
                    return Ok(AssumeOutcome::Decline);
                }
                let mut unknown: Option<&ClauseLiteral> = None;
                let mut unknown_count = 0usize;
                let mut satisfied = false;
                for literal in clause {
                    let truth = self.literal_truth(literal, state)?;
                    if self.meter.work.saturating_sub(entry_work) > MAX_INTERVAL_WORK {
                        return Ok(AssumeOutcome::Decline);
                    }
                    match truth {
                        Some(true) => {
                            satisfied = true;
                            break;
                        }
                        Some(false) => {}
                        None => {
                            unknown_count += 1;
                            unknown = Some(literal);
                        }
                    }
                }
                if satisfied {
                    continue;
                }
                // Every literal refuted: the authored clause is false.
                if unknown_count == 0 {
                    return self.confirm_interval_conflict(entry_work);
                }
                if unknown_count != 1 {
                    continue;
                }
                let Some(literal) = unknown else {
                    // The count and witness are maintained together, but this
                    // lane is only an additional authenticator: any internal
                    // inconsistency must decline rather than manufacture UNSAT.
                    return Ok(AssumeOutcome::Decline);
                };
                let outcome = self.assume_literal(literal, state)?;
                if self.meter.work.saturating_sub(entry_work) > MAX_INTERVAL_WORK {
                    return Ok(AssumeOutcome::Decline);
                }
                match outcome {
                    AssumeOutcome::Conflict => {
                        return self.confirm_interval_conflict(entry_work);
                    }
                    AssumeOutcome::Changed => changed = true,
                    AssumeOutcome::Stable => {}
                    AssumeOutcome::Decline => return Ok(AssumeOutcome::Decline),
                }
            }
            if !changed {
                break;
            }
        }
        Ok(AssumeOutcome::Stable)
    }

    /// A fresh deadline check also consumes work; check the share afterward.
    fn confirm_interval_conflict(
        &mut self,
        entry_work: u64,
    ) -> Result<AssumeOutcome, BvLiaUnsatAuthenticationError> {
        self.meter.check_entry()?;
        Ok(
            if self.meter.work.saturating_sub(entry_work) > MAX_INTERVAL_WORK {
                AssumeOutcome::Decline
            } else {
                AssumeOutcome::Conflict
            },
        )
    }
}
