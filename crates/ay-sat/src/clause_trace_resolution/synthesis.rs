// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Reconstruct one deterministic positive-RUP chain from the exact prior
/// canonical database and authenticated fixed units.
///
/// The target is negated into the initial assignment, then prior rows are
/// scanned in canonical-id order to a unit-propagation fixpoint, recording
/// the reason id of every propagated variable. On conflict the chain is
/// trimmed to the conflict CONE — only the reasons transitively supporting
/// the conflicting clause, emitted in propagation order followed by the
/// conflicting id — so the retained chain is minimal rather than one hint
/// per propagation the sweep happened to make. Each emitted id is unit (or
/// the final conflict) under the ids before it, so the ordinary independent
/// DAG replay accepts the same chain. `max_hints` caps the RETAINED chain;
/// `None` means the target was not RUP, or its cone did not fit that cap.
fn synthesize_rup_hints(
    original_clauses: &[(u64, Vec<Literal>)],
    derived: &[RupStep],
    target_clause: &[Literal],
    fixed_unit_premises: &[Literal],
    num_vars: usize,
    max_hints: usize,
    candidate_hint_capacity: usize,
    admitted_scratch_bytes: usize,
    meter: &mut ConversionMeter<'_>,
) -> Result<Option<Vec<u64>>, ResolutionValidationError> {
    let SynthesisState {
        mut assign,
        mut reason,
        mut order,
        mut in_cone,
    } = prepare_synthesis_state(
        num_vars,
        candidate_hint_capacity,
        admitted_scratch_bytes,
        meter,
    )?;

    if seed_synthesis_assignment(
        &mut assign,
        fixed_unit_premises,
        target_clause,
        num_vars,
        meter,
    )? {
        return Ok(Some(Vec::new()));
    }

    let Some(conflict_id) = sweep_synthesis_database(
        original_clauses,
        derived,
        &mut assign,
        &mut reason,
        &mut order,
        meter,
    )?
    else {
        return Ok(None);
    };

    finish_synthesized_chain(
        original_clauses,
        derived,
        conflict_id,
        &reason,
        &order,
        &mut in_cone,
        num_vars,
        max_hints,
        meter,
    )
}

fn finish_synthesized_chain(
    original_clauses: &[(u64, Vec<Literal>)],
    derived: &[RupStep],
    conflict_id: u64,
    reason: &[u64],
    order: &[u32],
    in_cone: &mut [u8],
    num_vars: usize,
    max_hints: usize,
    meter: &mut ConversionMeter<'_>,
) -> Result<Option<Vec<u64>>, ResolutionValidationError> {
    // Walk reasons transitively from the conflicting clause. Variables
    // assigned by the target negation or a fixed premise have reason 0 and
    // terminate the walk; the downstream replay installs those assignments.
    let mut stack: Vec<u32> = Vec::new();
    reserve_exact(
        &mut stack,
        num_vars,
        ResolutionValidationResource::AssignmentScratch,
        meter,
    )?;
    let mut cone_len = 0usize;
    let Some(conflict_clause) = prior_clause_by_id(original_clauses, derived, conflict_id) else {
        return Ok(None);
    };
    for &literal in conflict_clause {
        meter.charge(1)?;
        let variable = literal.variable().index();
        if reason[variable] != 0 && in_cone[variable] == 0 {
            in_cone[variable] = 1;
            cone_len += 1;
            stack.push(variable as u32);
        }
    }
    while let Some(variable) = stack.pop() {
        meter.charge(1)?;
        let Some(reason_clause) =
            prior_clause_by_id(original_clauses, derived, reason[variable as usize])
        else {
            continue;
        };
        for &literal in reason_clause {
            meter.charge(1)?;
            let support = literal.variable().index();
            if support != variable as usize && reason[support] != 0 && in_cone[support] == 0 {
                in_cone[support] = 1;
                cone_len += 1;
                stack.push(support as u32);
            }
        }
    }

    let chain_len = cone_len + 1;
    if chain_len > max_hints {
        return Ok(None);
    }
    let mut hints = Vec::new();
    reserve_exact(
        &mut hints,
        chain_len,
        ResolutionValidationResource::Hints,
        meter,
    )?;
    for &variable in order {
        meter.charge(1)?;
        if in_cone[variable as usize] != 0 {
            hints.push(reason[variable as usize]);
        }
    }
    hints.push(conflict_id);
    Ok(Some(hints))
}

/// Compact the producer's ordered hint candidates into a checked positive-RUP
/// chain under exact fixed premises.
///
/// Candidate ids remain untrusted. Named prior clauses are rescanned to a
/// deterministic fixpoint under fixed premises plus the negated target:
/// satisfied, open, and non-unit rows contribute no inference; unit rows are
/// retained once and propagated; the first conflict completes the chain. A
/// returned chain is never larger than the source candidate list and is still
/// replayed by the ordinary independent DAG validator before acceptance.
fn compact_rup_hint_candidates(
    original_clauses: &[(u64, Vec<Literal>)],
    derived: &[RupStep],
    target_clause: &[Literal],
    fixed_unit_premises: &[Literal],
    candidate_hints: &[u64],
    candidate_hint_capacity: usize,
    num_vars: usize,
    admitted_scratch_bytes: usize,
    meter: &mut ConversionMeter<'_>,
) -> Result<Option<Vec<u64>>, ResolutionValidationError> {
    let CompactionState {
        mut assign,
        mut hints,
        mut recorded,
    } = prepare_compaction_state(
        candidate_hints,
        candidate_hint_capacity,
        num_vars,
        admitted_scratch_bytes,
        meter,
    )?;

    if seed_synthesis_assignment(
        &mut assign,
        fixed_unit_premises,
        target_clause,
        num_vars,
        meter,
    )? {
        return Ok(Some(hints));
    }

    loop {
        let mut propagated = false;
        for (candidate_index, &id) in candidate_hints.iter().enumerate() {
            if candidate_index % CONTROL_POLL_INTERVAL == 0 {
                meter.check_controls()?;
            }
            meter.charge(1)?;
            if recorded[candidate_index] != 0 {
                continue;
            }
            let canonical_index = id
                .checked_sub(1)
                .and_then(|value| usize::try_from(value).ok());
            let clause = canonical_index.and_then(|index| {
                if let Some((stored_id, clause)) = original_clauses.get(index) {
                    (*stored_id == id).then_some(clause.as_slice())
                } else {
                    let derived_index = index.checked_sub(original_clauses.len())?;
                    let step = derived.get(derived_index)?;
                    (step.id == id).then_some(step.clause.as_slice())
                }
            });
            let Some(clause) = clause else {
                return Ok(None);
            };
            match scan_terminal_hint_clause(clause, &assign, meter)? {
                TerminalHintScan::Satisfied | TerminalHintScan::Open => {}
                TerminalHintScan::Unit(literal) => {
                    hints.push(id);
                    meter.charge(1)?;
                    recorded[candidate_index] = 1;
                    assign[literal.variable().index()] = Some(literal.is_positive());
                    propagated = true;
                }
                TerminalHintScan::Conflict => {
                    hints.push(id);
                    meter.charge(1)?;
                    return Ok(Some(hints));
                }
            }
        }
        if !propagated {
            return Ok(None);
        }
    }
}

struct SynthesisState {
    assign: Vec<Option<bool>>,
    reason: Vec<u64>,
    order: Vec<u32>,
    in_cone: Vec<u8>,
}

fn prepare_synthesis_state(
    num_vars: usize,
    candidate_hint_capacity: usize,
    admitted_scratch_bytes: usize,
    meter: &mut ConversionMeter<'_>,
) -> Result<SynthesisState, ResolutionValidationError> {
    let mut assign = Vec::new();
    reserve_exact(
        &mut assign,
        num_vars,
        ResolutionValidationResource::AssignmentScratch,
        meter,
    )?;
    // Cone bookkeeping: the canonical id that propagated each variable
    // (0 = unpropagated; canonical ids start at 1), the propagation order,
    // and the cone marker. All three are admitted by the planner's
    // propagation-scratch term.
    let mut reason: Vec<u64> = Vec::new();
    reserve_exact(
        &mut reason,
        num_vars,
        ResolutionValidationResource::AssignmentScratch,
        meter,
    )?;
    let mut order: Vec<u32> = Vec::new();
    reserve_exact(
        &mut order,
        num_vars,
        ResolutionValidationResource::AssignmentScratch,
        meter,
    )?;
    let mut in_cone: Vec<u8> = Vec::new();
    reserve_exact(
        &mut in_cone,
        num_vars,
        ResolutionValidationResource::AssignmentScratch,
        meter,
    )?;
    let actual_scratch_bytes = synthesis_scratch_bytes_from_capacities(
        assign.capacity(),
        candidate_hint_capacity,
        0,
        0,
        reason
            .capacity()
            .max(order.capacity())
            .max(in_cone.capacity()),
    )?;
    enforce_resource(
        ResolutionValidationResource::Bytes,
        actual_scratch_bytes,
        admitted_scratch_bytes,
    )?;
    while assign.len() < num_vars {
        let chunk = (num_vars - assign.len()).min(CONTROL_POLL_INTERVAL);
        meter.charge(chunk)?;
        assign.resize(assign.len() + chunk, None);
        reason.resize(reason.len() + chunk, 0);
        in_cone.resize(in_cone.len() + chunk, 0);
        meter.check_controls()?;
    }
    Ok(SynthesisState {
        assign,
        reason,
        order,
        in_cone,
    })
}

fn seed_synthesis_assignment(
    assign: &mut [Option<bool>],
    fixed_unit_premises: &[Literal],
    target_clause: &[Literal],
    num_vars: usize,
    meter: &mut ConversionMeter<'_>,
) -> Result<bool, ResolutionValidationError> {
    for &literal in fixed_unit_premises {
        meter.charge(1)?;
        let variable = literal.variable().index();
        if variable >= num_vars {
            return Err(ResolutionDagValidateError::VarOutOfRange {
                clause: 0,
                var: variable,
                num_vars,
            }
            .into());
        }
        let value = literal.is_positive();
        match assign[variable] {
            None => assign[variable] = Some(value),
            Some(existing) if existing == value => {}
            // The exact premise set refutes itself. The downstream replay has
            // the same fixed-premise conflict rule, so an empty hint chain is
            // a complete independently checked terminal derivation.
            Some(_) => return Ok(true),
        }
    }
    for &literal in target_clause {
        meter.charge(1)?;
        let variable = literal.variable().index();
        if variable >= num_vars {
            return Err(ResolutionDagValidateError::VarOutOfRange {
                clause: 0,
                var: variable,
                num_vars,
            }
            .into());
        }
        let value = !literal.is_positive();
        match assign[variable] {
            None => assign[variable] = Some(value),
            Some(existing) if existing == value => {}
            // The target is tautological under the fixed premises. Ordinary
            // RUP replay detects the same target-negation conflict immediately.
            Some(_) => return Ok(true),
        }
    }
    Ok(false)
}

fn sweep_synthesis_database(
    original_clauses: &[(u64, Vec<Literal>)],
    derived: &[RupStep],
    assign: &mut [Option<bool>],
    reason: &mut [u64],
    order: &mut Vec<u32>,
    meter: &mut ConversionMeter<'_>,
) -> Result<Option<u64>, ResolutionValidationError> {
    let conflict_id = 'sweep: loop {
        meter.check_controls()?;
        let mut propagated = false;
        let clauses = original_clauses
            .iter()
            .map(|(id, clause)| (*id, clause.as_slice()))
            .chain(derived.iter().map(|step| (step.id, step.clause.as_slice())));
        for (id, clause) in clauses {
            match scan_terminal_hint_clause(clause, assign, meter)? {
                TerminalHintScan::Satisfied | TerminalHintScan::Open => {}
                TerminalHintScan::Unit(literal) => {
                    // Unit scans only return an unassigned literal. Recording
                    // the reason id before installing the assignment keeps
                    // `order` aligned with positive-RUP propagation order.
                    let variable = literal.variable().index();
                    meter.charge(1)?;
                    reason[variable] = id;
                    order.push(variable as u32);
                    assign[variable] = Some(literal.is_positive());
                    propagated = true;
                }
                TerminalHintScan::Conflict => break 'sweep id,
            }
        }
        if !propagated {
            return Ok(None);
        }
    };
    Ok(Some(conflict_id))
}

struct CompactionState {
    assign: Vec<Option<bool>>,
    hints: Vec<u64>,
    recorded: Vec<u8>,
}

fn prepare_compaction_state(
    candidate_hints: &[u64],
    candidate_hint_capacity: usize,
    num_vars: usize,
    admitted_scratch_bytes: usize,
    meter: &mut ConversionMeter<'_>,
) -> Result<CompactionState, ResolutionValidationError> {
    let mut assign = Vec::new();
    reserve_exact(
        &mut assign,
        num_vars,
        ResolutionValidationResource::AssignmentScratch,
        meter,
    )?;
    while assign.len() < num_vars {
        let chunk = (num_vars - assign.len()).min(CONTROL_POLL_INTERVAL);
        meter.charge(chunk)?;
        assign.resize(assign.len() + chunk, None);
        meter.check_controls()?;
    }
    let mut hints = Vec::new();
    reserve_exact(
        &mut hints,
        candidate_hints.len(),
        ResolutionValidationResource::Hints,
        meter,
    )?;
    let mut recorded: Vec<u8> = Vec::new();
    reserve_exact(
        &mut recorded,
        candidate_hints.len(),
        ResolutionValidationResource::AssignmentScratch,
        meter,
    )?;
    for chunk in candidate_hints.chunks(CONTROL_POLL_INTERVAL) {
        meter.charge(chunk.len())?;
        recorded.resize(recorded.len() + chunk.len(), 0);
        meter.check_controls()?;
    }
    let actual_scratch_bytes = synthesis_scratch_bytes_from_capacities(
        assign.capacity(),
        candidate_hint_capacity,
        hints.capacity(),
        recorded.capacity(),
        0,
    )?;
    enforce_resource(
        ResolutionValidationResource::Bytes,
        actual_scratch_bytes,
        admitted_scratch_bytes,
    )?;
    Ok(CompactionState {
        assign,
        hints,
        recorded,
    })
}
