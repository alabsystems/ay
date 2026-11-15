// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// Frozen ordinary loop AFTER satisfied retirement and BEFORE scheduling.
// This is an ordering/work oracle, not independent proof authority.
pub(super) fn legacy_row(
    case: &Case,
    mut owner: CompactionScratch,
    target: &[Literal],
    premises: &[Literal],
    meter: &mut ConversionMeter<'_>,
) -> Result<(Option<Vec<u64>>, CompactionScratch), ResolutionValidationError> {
    meter.check_controls()?;
    let CompactionState {
        mut hints,
        mut recorded,
    } = prepare_compaction_state(
        &case.candidates,
        case.candidates.len(),
        planned_synthesis_scratch_bytes(owner.assign.len(), case.candidates.len())?,
        meter,
    )?;
    let found = owner.seed(premises, target, meter)?
        || legacy_sweep(case, &mut owner, &mut hints, &mut recorded, meter)?;
    owner.clear(meter)?;
    Ok((found.then_some(hints), owner))
}

fn legacy_sweep(
    case: &Case,
    owner: &mut CompactionScratch,
    hints: &mut Vec<u64>,
    recorded: &mut [u8],
    meter: &mut ConversionMeter<'_>,
) -> Result<bool, ResolutionValidationError> {
    loop {
        let mut propagated = false;
        for (position, &id) in case.candidates.iter().enumerate() {
            if position % CONTROL_POLL_INTERVAL == 0 {
                meter.check_controls()?;
            }
            meter.charge(1)?;
            if recorded[position] != 0 {
                continue;
            }
            let Some(clause) = prior_clause_by_id(&case.originals, &case.derived, id) else {
                return Ok(false);
            };
            match scan_terminal_hint_clause(clause, &owner.assign, meter)? {
                TerminalHintScan::Satisfied => {
                    meter.charge(1)?;
                    recorded[position] = 1;
                }
                TerminalHintScan::Open => {}
                TerminalHintScan::Unit(literal) => {
                    hints.push(id);
                    meter.charge(1)?;
                    recorded[position] = 1;
                    owner.set_unassigned(literal.variable(), literal.is_positive(), meter)?;
                    propagated = true;
                }
                TerminalHintScan::Conflict => {
                    hints.push(id);
                    meter.charge(1)?;
                    return Ok(true);
                }
            }
        }
        if !propagated {
            return Ok(false);
        }
    }
}
