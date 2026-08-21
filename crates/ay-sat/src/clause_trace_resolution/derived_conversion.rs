// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

struct DerivedConversion {
    steps: Vec<RupStep>,
    empty_clause_id: u64,
}

struct DerivedConversionInputs<'a> {
    entries: TraceEntries<'a>,
    original_clauses: &'a [(u64, Vec<Literal>)],
    unit_premises: &'a [Literal],
    terminal_empty_index: Option<usize>,
    shape: TraceShape,
    num_vars: usize,
}

struct DerivedConversionState {
    steps: Vec<RupStep>,
    next_canonical_id: u64,
    empty_clause_id: Option<u64>,
    widening_hint_slack: usize,
    widening_byte_slack: usize,
    reconstruction_row_bound: usize,
    root_state: Option<RootPropagation>,
}

fn convert_derived_clauses(
    inputs: DerivedConversionInputs<'_>,
    entry_states: &mut HashMap<u64, TraceIdState>,
    next_canonical_id: u64,
    meter: &mut ConversionMeter<'_>,
) -> Result<DerivedConversion, ClauseTraceResolutionError> {
    let mut steps = Vec::new();
    reserve_exact(
        &mut steps,
        inputs.shape.derived_steps,
        ResolutionValidationResource::DerivedSteps,
        meter,
    )?;
    let reconstruction_row_bound = inputs.entries.len().min(checked_resource_add(
        inputs.num_vars,
        1,
        ResolutionValidationResource::Hints,
    )?);
    let mut state = DerivedConversionState {
        steps,
        next_canonical_id,
        empty_clause_id: None,
        widening_hint_slack: inputs.shape.widening_hint_slack,
        widening_byte_slack: inputs.shape.widening_byte_slack,
        reconstruction_row_bound,
        root_state: None,
    };
    for (entry_index, entry) in inputs.entries.iter().enumerate() {
        meter.charge(1)?;
        if entry.is_original {
            continue;
        }
        convert_derived_entry(entry_index, entry, &inputs, entry_states, &mut state, meter)?;
    }
    if inputs.shape.synthesize_terminal_empty {
        append_synthesized_terminal(&inputs, &mut state, meter)?;
    }
    let empty_clause_id = state
        .empty_clause_id
        .ok_or(ClauseTraceResolutionError::EmptyMarkerWithoutDerivedEmpty)?;
    Ok(DerivedConversion {
        steps: state.steps,
        empty_clause_id,
    })
}

fn convert_derived_entry(
    entry_index: usize,
    entry: crate::clause_trace::ClauseTraceEntryRef<'_>,
    inputs: &DerivedConversionInputs<'_>,
    entry_states: &mut HashMap<u64, TraceIdState>,
    state: &mut DerivedConversionState,
    meter: &mut ConversionMeter<'_>,
) -> Result<(), ClauseTraceResolutionError> {
    meter.charge(1)?;
    let canonical_id = state.next_canonical_id;
    state.next_canonical_id = state
        .next_canonical_id
        .checked_add(1)
        .ok_or(ClauseTraceResolutionError::CanonicalIdOverflow)?;
    let candidates = canonical_hint_candidates(entry_index, entry, entry_states, meter)?;
    let repaired = repair_derived_hints(
        entry,
        inputs,
        state,
        &candidates,
        candidates.capacity(),
        meter,
    )?;
    let rup_hints = retain_repaired_hints(
        repaired,
        candidates,
        entry.resolution_hints.len(),
        inputs.shape.row_hint_budget,
        &mut state.widening_hint_slack,
        &mut state.widening_byte_slack,
    )?;
    let checked_state = entry_states.get_mut(&entry.id).ok_or(
        ClauseTraceResolutionError::MissingCheckedIdentity {
            entry_index,
            id: entry.id,
        },
    )?;
    checked_state.canonical_id = Some(canonical_id);
    if Some(entry_index) == inputs.terminal_empty_index {
        state.empty_clause_id = Some(canonical_id);
    }
    let clause = copy_slice_bounded(
        entry.clause,
        ResolutionValidationResource::DerivedLiterals,
        meter,
    )?;
    state.steps.push(RupStep {
        id: canonical_id,
        clause,
        rup_hints,
    });
    Ok(())
}

fn canonical_hint_candidates(
    entry_index: usize,
    entry: crate::clause_trace::ClauseTraceEntryRef<'_>,
    entry_states: &HashMap<u64, TraceIdState>,
    meter: &mut ConversionMeter<'_>,
) -> Result<Vec<u64>, ClauseTraceResolutionError> {
    let mut candidates = Vec::new();
    reserve_exact(
        &mut candidates,
        entry.resolution_hints.len(),
        ResolutionValidationResource::Hints,
        meter,
    )?;
    for (hint_index, &hint_id) in entry.resolution_hints.iter().enumerate() {
        if hint_index % CONTROL_POLL_INTERVAL == 0 {
            meter.check_controls()?;
        }
        meter.charge(1)?;
        let canonical_hint = entry_states
            .get(&hint_id)
            .and_then(|state| state.canonical_id)
            .ok_or(ClauseTraceResolutionError::UnknownHint {
                entry_index,
                entry_id: entry.id,
                hint_id,
            })?;
        candidates.push(canonical_hint);
    }
    Ok(candidates)
}

fn repair_derived_hints(
    entry: crate::clause_trace::ClauseTraceEntryRef<'_>,
    inputs: &DerivedConversionInputs<'_>,
    state: &mut DerivedConversionState,
    candidates: &[u64],
    candidate_capacity: usize,
    meter: &mut ConversionMeter<'_>,
) -> Result<Option<Vec<u64>>, ResolutionValidationError> {
    let compacted = compact_rup_hint_candidates(
        inputs.original_clauses,
        &state.steps,
        entry.clause,
        inputs.unit_premises,
        candidates,
        candidate_capacity,
        inputs.num_vars,
        inputs.shape.synthesis_scratch_bytes,
        meter,
    )?;
    if compacted.is_some() {
        return Ok(compacted);
    }
    let admitted_row_hints = entry
        .resolution_hints
        .len()
        .max(inputs.shape.row_hint_budget);
    let slack_hints = state
        .widening_hint_slack
        .min(state.widening_byte_slack / size_of::<u64>());
    let synthesis_cap = admitted_row_hints.max(
        state
            .reconstruction_row_bound
            .min(admitted_row_hints.saturating_add(slack_hints)),
    );
    if state.root_state.is_none() {
        state.root_state = Some(compute_root_propagation(
            inputs.original_clauses,
            inputs.unit_premises,
            inputs.num_vars,
            meter,
        )?);
    }
    let rooted = match state.root_state.as_mut() {
        Some(root) => compact_rup_hint_candidates_rooted(
            root,
            inputs.original_clauses,
            &state.steps,
            entry.clause,
            candidates,
            synthesis_cap,
            meter,
        )?,
        None => None,
    };
    if rooted.is_some() {
        return Ok(rooted);
    }
    synthesize_rup_hints(
        inputs.original_clauses,
        &state.steps,
        entry.clause,
        inputs.unit_premises,
        inputs.num_vars,
        synthesis_cap,
        candidate_capacity,
        inputs.shape.synthesis_scratch_bytes,
        meter,
    )
}

fn retain_repaired_hints(
    repaired: Option<Vec<u64>>,
    candidates: Vec<u64>,
    recorded_hint_count: usize,
    row_hint_budget: usize,
    widening_hint_slack: &mut usize,
    widening_byte_slack: &mut usize,
) -> Result<Vec<u64>, ResolutionValidationError> {
    let Some(hints) = repaired else {
        return Ok(candidates);
    };
    let admitted_row_hints = recorded_hint_count.max(row_hint_budget);
    let excess = hints.len().saturating_sub(admitted_row_hints);
    if excess == 0 {
        return Ok(hints);
    }
    let excess_bytes = checked_resource_mul(
        excess,
        size_of::<u64>(),
        ResolutionValidationResource::Bytes,
    )?;
    if excess <= *widening_hint_slack && excess_bytes <= *widening_byte_slack {
        *widening_hint_slack -= excess;
        *widening_byte_slack -= excess_bytes;
        Ok(hints)
    } else {
        Ok(candidates)
    }
}

fn append_synthesized_terminal(
    inputs: &DerivedConversionInputs<'_>,
    state: &mut DerivedConversionState,
    meter: &mut ConversionMeter<'_>,
) -> Result<(), ClauseTraceResolutionError> {
    let rup_hints = synthesize_terminal_empty_hints(
        inputs.original_clauses,
        &state.steps,
        inputs.unit_premises,
        inputs.num_vars,
        inputs.shape.synthesis_scratch_bytes,
        meter,
    )?;
    let canonical_id = state.next_canonical_id;
    state.steps.push(RupStep {
        id: canonical_id,
        clause: Vec::new(),
        rup_hints,
    });
    state.empty_clause_id = Some(canonical_id);
    Ok(())
}
