// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(in super::super) enum CandidateSchedule {
    Pending,
    Legacy,
    Exhausted,
    Indexed(Scheduler),
}

impl CandidateSchedule {
    pub(in super::super) fn indexed(&mut self) -> Option<&mut Scheduler> {
        match self {
            Self::Indexed(scheduler) => Some(scheduler),
            _ => None,
        }
    }

    /// Decide once, only after the first sweep and the current original CSR
    /// cascade. No new namespace-sized scratch is needed for this census.
    pub(in super::super) fn select(
        root: &RootPropagation,
        originals: &[(u64, Vec<Literal>)],
        derived: &[RupStep],
        candidates: &[u64],
        retired: &rooted_retirement::RetiredCandidates,
        admitted: usize,
        meter: &mut ConversionMeter<'_>,
    ) -> Result<Option<Self>, ResolutionValidationError> {
        meter.check_controls()?;
        let before = meter.consumed_work();
        let mut remaining = Some(0u128);
        let mut literals = Some(0u128);
        for (position, &id) in candidates.iter().enumerate() {
            meter.charge(1)?;
            if retired.contains(position) {
                continue;
            }
            meter.charge(1)?;
            let Some(clause) = prior_clause_by_id(originals, derived, id) else {
                return Ok(None);
            };
            remaining = remaining.and_then(|count| count.checked_add(1));
            literals = literals.and_then(|count| count.checked_add(clause.len() as u128));
        }
        meter.charge(1)?;
        let selector_work = u128::from(meter.consumed_work() - before);
        meter.check_controls()?;
        if remaining == Some(0) {
            // Retirement is monotone within this row. Only the candidate
            // lane is exhausted: its caller must still drain the originals.
            return Ok(Some(Self::Exhausted));
        }
        if remaining
            .zip(literals)
            .is_some_and(|(remaining, literals)| {
                legacy_is_cheaper(
                    candidates.len() as u128,
                    remaining,
                    literals,
                    root.assign.len() as u128,
                    selector_work,
                )
            })
        {
            return Ok(Some(Self::Legacy));
        }
        Ok(Scheduler::new(
            root, originals, derived, candidates, retired, admitted, meter,
        )?
        .map(Self::Indexed))
    }
}

/// M remaining positions can propagate at most M times. In addition to a
/// terminating pass, rooted repair can have one nonpropagating pass that
/// escalates to the original CSR. Every other round needs a candidate unit:
/// the original cascade drains its whole trail before candidates run.
///
/// Each pass costs at most C position visits, M scanner entries and L literal
/// reads; lifetime retirement/assignment costs at most 2M. Include the actual
/// selector debit, and compare with the unavoidable three D=2V+1 head passes.
pub(super) fn legacy_is_cheaper(
    candidates: u128,
    remaining: u128,
    literals: u128,
    num_vars: u128,
    selector_work: u128,
) -> bool {
    let bound = (|| {
        let round = candidates.checked_add(remaining)?.checked_add(literals)?;
        remaining
            .checked_add(2)?
            .checked_mul(round)?
            .checked_add(remaining.checked_mul(2)?)?
            .checked_add(1)?
            .checked_add(selector_work)
    })();
    let setup = num_vars
        .checked_mul(2)
        .and_then(|count| count.checked_add(1))
        .and_then(|count| count.checked_mul(3));
    matches!((bound, setup), (Some(bound), Some(setup)) if bound <= setup)
}
