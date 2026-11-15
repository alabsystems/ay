// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

// Frozen test-only full-synthesis sweep: no retirement. Preparation, seeding,
// scanner and cone assembly are shared, but independent DAG replay separately
// checks the produced chain against the originals and earlier derived steps.
pub(super) fn sweep(
    originals: &[(u64, Vec<Literal>)],
    derived: &[RupStep],
    assign: &mut [Option<bool>],
    reason: &mut [u64],
    order: &mut Vec<u32>,
    meter: &mut ConversionMeter<'_>,
) -> Result<Option<u64>, ResolutionValidationError> {
    loop {
        meter.check_controls()?;
        let mut propagated = false;
        let clauses = originals
            .iter()
            .map(|(id, clause)| (*id, clause.as_slice()))
            .chain(derived.iter().map(|step| (step.id, step.clause.as_slice())));
        for (id, clause) in clauses {
            match scan_terminal_hint_clause(clause, assign, meter)? {
                TerminalHintScan::Satisfied | TerminalHintScan::Open => {}
                TerminalHintScan::Unit(literal) => {
                    let variable = literal.variable().index();
                    meter.charge(1)?;
                    reason[variable] = id;
                    order.push(variable as u32);
                    assign[variable] = Some(literal.is_positive());
                    propagated = true;
                }
                TerminalHintScan::Conflict => return Ok(Some(id)),
            }
        }
        if !propagated {
            return Ok(None);
        }
    }
}

pub(super) fn synthesize(
    fixture: &Fixture,
    target: &[Literal],
    meter: &mut ConversionMeter<'_>,
) -> Result<Option<Vec<u64>>, ResolutionValidationError> {
    let mut state = prepare_synthesis_state(
        fixture.num_vars,
        0,
        planned_synthesis_scratch_bytes(fixture.num_vars, 0)?,
        meter,
    )?;
    if seed_synthesis_assignment(&mut state.assign, &[], target, fixture.num_vars, meter)? {
        return Ok(Some(vec![]));
    }
    let Some(conflict) = sweep(
        &fixture.originals,
        &fixture.derived,
        &mut state.assign,
        &mut state.reason,
        &mut state.order,
        meter,
    )?
    else {
        return Ok(None);
    };
    finish_synthesized_chain(
        &fixture.originals,
        &fixture.derived,
        conflict,
        &state.reason,
        &state.order,
        &mut state.in_cone,
        fixture.num_vars,
        usize::MAX,
        meter,
    )
}
