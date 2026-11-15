// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Candidate-only RUP propagation with the legacy ascending-position rounds.

use super::*;

enum CandidateOrder {
    FirstPass,
    Legacy,
    Indexed(rooted_scheduler::Scheduler),
}

pub(super) fn compact_seeded_candidates(
    original_clauses: &[(u64, Vec<Literal>)],
    derived: &[RupStep],
    candidate_hints: &[u64],
    scratch: &mut CompactionScratch,
    hints: &mut Vec<u64>,
    recorded: &mut [u8],
    admitted_scheduler_bytes: usize,
    meter: &mut ConversionMeter<'_>,
) -> Result<bool, ResolutionValidationError> {
    let mut order = CandidateOrder::FirstPass;
    loop {
        let mut propagated = false;
        let mut open = false;
        let mut cursor = 0;
        loop {
            let candidate_index = if let CandidateOrder::Indexed(ready) = &mut order {
                let Some(position) = ready.pop(meter)? else {
                    break;
                };
                position
            } else {
                if cursor == candidate_hints.len() {
                    break;
                }
                let position = cursor;
                cursor += 1;
                position
            };
            if candidate_index % CONTROL_POLL_INTERVAL == 0 {
                meter.check_controls()?;
            }
            meter.charge(1)?;
            if recorded[candidate_index] != 0 {
                continue;
            }
            let id = candidate_hints[candidate_index];
            let Some(clause) = prior_clause_by_id(original_clauses, derived, id) else {
                return Ok(false);
            };
            match scan_terminal_hint_clause(clause, &scratch.assign, meter)? {
                TerminalHintScan::Satisfied => {
                    meter.charge(1)?;
                    recorded[candidate_index] = 1;
                }
                TerminalHintScan::Open => open = true,
                TerminalHintScan::Unit(literal) => {
                    hints.push(id);
                    meter.charge(1)?;
                    recorded[candidate_index] = 1;
                    scratch.set_unassigned(literal.variable(), literal.is_positive(), meter)?;
                    propagated = true;
                    if let CandidateOrder::Indexed(ready) = &mut order {
                        meter.charge(1)?;
                        ready.notify_assignment(
                            literal.variable().index(),
                            literal.is_positive(),
                            Some(candidate_index),
                            |position| recorded[position] != 0,
                            meter,
                        )?;
                    }
                }
                TerminalHintScan::Conflict => {
                    hints.push(id);
                    meter.charge(1)?;
                    return Ok(true);
                }
            }
        }
        if !propagated || (matches!(order, CandidateOrder::FirstPass) && !open) {
            return Ok(false);
        }
        match &mut order {
            CandidateOrder::Indexed(ready) => ready.next_round(meter)?,
            CandidateOrder::Legacy => {}
            CandidateOrder::FirstPass => {
                let Some(selected) = select_order(
                    scratch.assign.len(),
                    original_clauses,
                    derived,
                    candidate_hints,
                    recorded,
                    admitted_scheduler_bytes,
                    meter,
                )?
                else {
                    return Ok(false);
                };
                order = selected;
            }
        }
    }
}

fn select_order(
    num_vars: usize,
    originals: &[(u64, Vec<Literal>)],
    derived: &[RupStep],
    candidates: &[u64],
    recorded: &[u8],
    admitted: usize,
    meter: &mut ConversionMeter<'_>,
) -> Result<Option<CandidateOrder>, ResolutionValidationError> {
    // Census only after a complete first sweep needs continuation. Count
    // positions, not distinct ids; no namespace-sized allocation is needed.
    let before = meter.consumed_work();
    let mut remaining = Some(0u128);
    let mut literals = Some(0u128);
    for (position, &id) in candidates.iter().enumerate() {
        meter.charge(1)?;
        if recorded[position] != 0 {
            continue;
        }
        meter.charge(1)?;
        let Some(clause) = prior_clause_by_id(originals, derived, id) else {
            return Ok(None);
        };
        remaining = remaining.and_then(|count| count.checked_add(1));
        literals = literals.and_then(|sum| sum.checked_add(clause.len() as u128));
    }
    meter.charge(1)?;
    let selector_work = u128::from(meter.consumed_work() - before);
    if remaining
        .zip(literals)
        .is_some_and(|(remaining, literals)| {
            legacy_is_cheaper(
                candidates.len() as u128,
                remaining,
                literals,
                num_vars as u128,
                selector_work,
            )
        })
    {
        return Ok(Some(CandidateOrder::Legacy));
    }
    // All unretired positions start ready, covering assignments made before
    // the index existed. This owner drops before scratch cleanup or fallback.
    Ok(rooted_scheduler::Scheduler::for_candidates(
        num_vars,
        originals,
        derived,
        candidates,
        |position| recorded[position] != 0,
        admitted,
        meter,
    )?
    .map(CandidateOrder::Indexed))
}

/// At most M remaining positions can propagate, so legacy uses at most M+1
/// rounds. Each visits C positions, enters M scanners and reads at most L
/// literals. Lifetime retirement/unit writes cost at most 2M, plus one conflict.
/// Dense CSR must initialize, prefix-sum and copy D=2V+1 heads. Including the
/// selector's own debits, bypass only when this entire upper bound fits in 3D.
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
            .checked_add(1)?
            .checked_mul(round)?
            .checked_add(remaining.checked_mul(2)?)?
            .checked_add(1)?
            .checked_add(selector_work)
    })();
    let setup = num_vars
        .checked_mul(2)
        .and_then(|n| n.checked_add(1))
        .and_then(|n| n.checked_mul(3));
    matches!((bound, setup), (Some(bound), Some(setup)) if bound <= setup)
}
