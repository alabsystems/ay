// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

fn validate_clause_trace_resolution_interruptible_impl(
    trace: &ClauseTrace,
    num_vars: usize,
    fixed_unit_premises: &[Literal],
    limits: &ResolutionValidationLimits,
    mut should_stop: impl FnMut() -> bool,
) -> Result<(ValidatedClauseTraceResolution, Vec<Literal>), ClauseTraceResolutionError> {
    let mut meter = ConversionMeter::new(limits, &mut should_stop)?;
    ensure_trace_available(trace)?;

    let entries = trace.entries();
    let PreparedPremises {
        shape,
        unit_premises,
        retained_premise_bytes,
    } = meter.in_phase(ConversionPhase::Preflight, |meter| {
        prepare_fixed_unit_premises(trace, entries, num_vars, fixed_unit_premises, meter)
    })?;
    let mut entry_states = meter.in_phase(ConversionPhase::Namespace, |meter| {
        collect_entry_states(entries, meter)
    })?;
    let structure = meter.in_phase(ConversionPhase::Namespace, |meter| {
        validate_entry_structure(trace, entries, &unit_premises, &entry_states, shape, meter)
    })?;
    let shape = meter.in_phase(ConversionPhase::Preflight, |meter| {
        admit_candidate_scheduler(
            shape,
            structure.max_candidate_count,
            structure.max_candidate_literals,
            entries.len(),
            num_vars,
            retained_premise_bytes,
            meter,
        )
    })?;
    let OriginalConversion {
        clauses: original_clauses,
        mappings: original_mappings,
        next_canonical_id,
    } = meter.in_phase(ConversionPhase::Originals, |meter| {
        convert_original_clauses(entries, shape, &mut entry_states, meter)
    })?;
    let DerivedConversion {
        steps: derived,
        empty_clause_id,
    } = meter.in_phase(ConversionPhase::Derived, |meter| {
        convert_derived_clauses(
            DerivedConversionInputs {
                entries,
                original_clauses: &original_clauses,
                unit_premises: &unit_premises,
                terminal_empty_index: structure.terminal_empty_index,
                shape,
                num_vars,
            },
            &mut entry_states,
            next_canonical_id,
            meter,
        )
    })?;
    let FinalizedConversion {
        dag,
        original_mappings,
        retained_bytes,
        replay_additional_bytes,
    } = meter.in_phase(ConversionPhase::Finalize, |meter| {
        finalize_converted_trace(
            ConversionPayload {
                num_vars,
                original_clauses,
                original_mappings,
                derived,
                empty_clause_id,
                entry_states,
                retained_premise_bytes,
                source_trace_bytes: shape.source_trace_bytes,
            },
            meter,
        )
    })?;

    let conversion_work = meter.consumed_work();
    let validation_work = replay_converted_dag(
        &dag,
        limits,
        &unit_premises,
        replay_additional_bytes,
        conversion_work,
        &mut should_stop,
    )?;
    Ok((
        ValidatedClauseTraceResolution {
            dag,
            original_mappings,
            validation_work,
            retained_bytes,
        },
        unit_premises,
    ))
}

fn ensure_trace_available(trace: &ClauseTrace) -> Result<(), ClauseTraceResolutionError> {
    if trace.is_truncated() {
        return Err(ClauseTraceResolutionError::Truncated);
    }
    // A plainly exhausted trace was discarded mid-search and cannot be
    // complete. A literals-only exhausted trace kept the full clause
    // sequence (hints stripped): admission only reaches the repair lanes,
    // and the independent DAG replay remains the sole authority.
    if trace.proof_work_exhausted() && !trace.literals_only_recording() {
        return Err(ClauseTraceResolutionError::ProofWorkExhausted);
    }
    Ok(())
}

struct PreparedPremises {
    shape: TraceShape,
    unit_premises: Vec<Literal>,
    retained_premise_bytes: usize,
}

fn prepare_fixed_unit_premises(
    trace: &ClauseTrace,
    entries: TraceEntries<'_>,
    num_vars: usize,
    fixed_unit_premises: &[Literal],
    meter: &mut ConversionMeter<'_>,
) -> Result<PreparedPremises, ClauseTraceResolutionError> {
    let premise_payload_bytes = checked_resource_mul(
        fixed_unit_premises.len(),
        size_of::<Literal>(),
        ResolutionValidationResource::Bytes,
    )?;
    let planned_premise_bytes = checked_resource_add(
        size_of::<Vec<Literal>>(),
        checked_resource_mul(
            premise_payload_bytes,
            2,
            ResolutionValidationResource::Bytes,
        )?,
        ResolutionValidationResource::Bytes,
    )?;
    let shape = preflight_trace_shape(
        trace,
        entries,
        num_vars,
        planned_premise_bytes,
        !fixed_unit_premises.is_empty(),
        meter,
    )?;
    enforce_resource(
        ResolutionValidationResource::OriginalClauses,
        checked_resource_add(
            shape.original_clauses,
            fixed_unit_premises.len(),
            ResolutionValidationResource::OriginalClauses,
        )?,
        meter.limits.max_original_clauses,
    )?;
    enforce_resource(
        ResolutionValidationResource::OriginalLiterals,
        checked_resource_add(
            shape.original_literals,
            fixed_unit_premises.len(),
            ResolutionValidationResource::OriginalLiterals,
        )?,
        meter.limits.max_original_literals,
    )?;
    for (premise_index, &premise) in fixed_unit_premises.iter().enumerate() {
        if premise_index % CONTROL_POLL_INTERVAL == 0 {
            meter.check_controls()?;
        }
        meter.charge(1)?;
        let variable = premise.variable().index();
        if variable >= num_vars {
            return Err(ClauseTraceResolutionError::UnitPremiseVariableOutOfRange {
                premise_index,
                variable,
                num_vars,
            });
        }
    }
    let unit_premises = copy_slice_bounded(
        fixed_unit_premises,
        ResolutionValidationResource::OriginalLiterals,
        meter,
    )?;
    let retained_premise_bytes = checked_resource_add(
        size_of::<Vec<Literal>>(),
        checked_resource_add(
            premise_payload_bytes,
            checked_resource_mul(
                unit_premises.capacity(),
                size_of::<Literal>(),
                ResolutionValidationResource::Bytes,
            )?,
            ResolutionValidationResource::Bytes,
        )?,
        ResolutionValidationResource::Bytes,
    )?;
    enforce_resource(
        ResolutionValidationResource::Bytes,
        retained_premise_bytes,
        meter.limits.max_bytes,
    )?;
    Ok(PreparedPremises {
        shape,
        unit_premises,
        retained_premise_bytes,
    })
}

fn collect_entry_states(
    entries: TraceEntries<'_>,
    meter: &mut ConversionMeter<'_>,
) -> Result<HashMap<u64, TraceIdState>, ClauseTraceResolutionError> {
    let mut states = HashMap::new();
    meter.check_controls()?;
    meter.charge(checked_resource_mul(
        entries.len(),
        2,
        ResolutionValidationResource::Work,
    )?)?;
    states
        .try_reserve(entries.len())
        .map_err(|_| ResolutionValidationError::AllocationFailed {
            resource: ResolutionValidationResource::ClauseDatabase,
        })?;
    meter.check_controls()?;
    for (entry_index, entry) in entries.iter().enumerate() {
        if entry_index % CONTROL_POLL_INTERVAL == 0 {
            meter.check_controls()?;
        }
        meter.charge(1)?;
        if entry.id == 0 {
            return Err(ClauseTraceResolutionError::ZeroClauseId { entry_index });
        }
        if let Some(first) = states.insert(
            entry.id,
            TraceIdState {
                trace_index: entry_index,
                canonical_id: None,
            },
        ) {
            return Err(ClauseTraceResolutionError::DuplicateClauseId {
                id: entry.id,
                first_index: first.trace_index,
                duplicate_index: entry_index,
            });
        }
    }
    Ok(states)
}

struct CheckedTraceStructure {
    terminal_empty_index: Option<usize>,
    max_candidate_count: usize,
    max_candidate_literals: usize,
}

fn validate_entry_structure(
    trace: &ClauseTrace,
    entries: TraceEntries<'_>,
    unit_premises: &[Literal],
    entry_states: &HashMap<u64, TraceIdState>,
    shape: TraceShape,
    meter: &mut ConversionMeter<'_>,
) -> Result<CheckedTraceStructure, ClauseTraceResolutionError> {
    let mut terminal_empty_index = None;
    let mut max_candidate_count = 0;
    let mut max_candidate_literals = 0;
    for (entry_index, entry) in entries.iter().enumerate() {
        if entry_index % CONTROL_POLL_INTERVAL == 0 {
            meter.check_controls()?;
        }
        meter.charge(1)?;
        if let Some(empty_entry_index) = terminal_empty_index {
            return Err(ClauseTraceResolutionError::EntryAfterTerminalEmpty {
                entry_index,
                id: entry.id,
                empty_entry_index,
            });
        }
        if entry.is_original {
            validate_original_entry(entry_index, entry)?;
            continue;
        }
        // A literals-only trace (post-#A2b-degradation) records no hints by
        // construction; its rows reach the repair lanes with empty
        // candidates instead of being structurally refused here.
        if entry.resolution_hints.is_empty()
            && unit_premises.is_empty()
            && !trace.literals_only_recording()
        {
            return Err(ClauseTraceResolutionError::UnhintedDerivedClause {
                entry_index,
                id: entry.id,
            });
        }
        let literals = validate_entry_hints(entry_index, entry, entries, entry_states, meter)?;
        max_candidate_count = max_candidate_count.max(entry.resolution_hints.len());
        max_candidate_literals = max_candidate_literals.max(literals);
        if entry.clause.is_empty() {
            terminal_empty_index = Some(entry_index);
        }
    }
    if terminal_empty_index.is_none() && !shape.synthesize_terminal_empty {
        return if trace.has_empty_clause() {
            Err(ClauseTraceResolutionError::EmptyMarkerWithoutDerivedEmpty)
        } else {
            Err(ClauseTraceResolutionError::NoDerivedEmptyClause)
        };
    }
    if !trace.has_empty_clause() {
        return Err(ClauseTraceResolutionError::NoDerivedEmptyClause);
    }
    Ok(CheckedTraceStructure {
        terminal_empty_index,
        max_candidate_count,
        max_candidate_literals,
    })
}

fn validate_original_entry(
    entry_index: usize,
    entry: crate::clause_trace::ClauseTraceEntryRef<'_>,
) -> Result<(), ClauseTraceResolutionError> {
    if entry.clause.is_empty() {
        return Err(ClauseTraceResolutionError::OriginalEmptyClause {
            entry_index,
            id: entry.id,
        });
    }
    if !entry.resolution_hints.is_empty() {
        return Err(ClauseTraceResolutionError::OriginalHasHints {
            entry_index,
            id: entry.id,
        });
    }
    Ok(())
}

fn validate_entry_hints(
    entry_index: usize,
    entry: crate::clause_trace::ClauseTraceEntryRef<'_>,
    entries: TraceEntries<'_>,
    entry_states: &HashMap<u64, TraceIdState>,
    meter: &mut ConversionMeter<'_>,
) -> Result<usize, ClauseTraceResolutionError> {
    let mut literals = 0;
    for (hint_index, &hint_id) in entry.resolution_hints.iter().enumerate() {
        if hint_index % CONTROL_POLL_INTERVAL == 0 {
            meter.check_controls()?;
        }
        meter.charge(1)?;
        if hint_id == 0 {
            return Err(ClauseTraceResolutionError::ZeroHint {
                entry_index,
                entry_id: entry.id,
            });
        }
        let Some(hint_state) = entry_states.get(&hint_id) else {
            return Err(ClauseTraceResolutionError::UnknownHint {
                entry_index,
                entry_id: entry.id,
                hint_id,
            });
        };
        if hint_state.trace_index >= entry_index {
            return Err(ClauseTraceResolutionError::FutureHint {
                entry_index,
                entry_id: entry.id,
                hint_id,
                hint_entry_index: hint_state.trace_index,
            });
        }
        // Count positions, not distinct ids: duplicate hints produce distinct
        // scheduler positions and repeated occurrences. No second map needed.
        meter.charge(1)?;
        meter.charge(entries.lookup_work_bound())?;
        let hinted = entries.get(hint_state.trace_index).ok_or(
            ClauseTraceResolutionError::MissingCheckedIdentity {
                entry_index: hint_state.trace_index,
                id: hint_id,
            },
        )?;
        literals = checked_resource_add(
            literals,
            hinted.clause.len(),
            ResolutionValidationResource::Bytes,
        )?;
    }
    Ok(literals)
}

struct OriginalConversion {
    clauses: Vec<(u64, Vec<Literal>)>,
    mappings: Vec<ClauseTraceOriginalMapping>,
    next_canonical_id: u64,
}

fn convert_original_clauses(
    entries: TraceEntries<'_>,
    shape: TraceShape,
    entry_states: &mut HashMap<u64, TraceIdState>,
    meter: &mut ConversionMeter<'_>,
) -> Result<OriginalConversion, ClauseTraceResolutionError> {
    let mut clauses = Vec::new();
    reserve_exact(
        &mut clauses,
        shape.original_clauses,
        ResolutionValidationResource::OriginalClauses,
        meter,
    )?;
    let mut mappings = Vec::new();
    reserve_exact(
        &mut mappings,
        shape.original_clauses,
        ResolutionValidationResource::OriginalClauses,
        meter,
    )?;
    let mut next_canonical_id = 1_u64;
    for (trace_index, entry) in entries.iter().enumerate() {
        meter.charge(1)?;
        if !entry.is_original {
            continue;
        }
        meter.charge(1)?;
        let canonical_id = next_canonical_id;
        next_canonical_id = next_canonical_id
            .checked_add(1)
            .ok_or(ClauseTraceResolutionError::CanonicalIdOverflow)?;
        let state = entry_states.get_mut(&entry.id).ok_or(
            ClauseTraceResolutionError::MissingCheckedIdentity {
                entry_index: trace_index,
                id: entry.id,
            },
        )?;
        state.canonical_id = Some(canonical_id);
        let dag_clause = copy_slice_bounded(
            entry.clause,
            ResolutionValidationResource::OriginalLiterals,
            meter,
        )?;
        let mapped_clause = copy_slice_bounded(
            entry.clause,
            ResolutionValidationResource::OriginalLiterals,
            meter,
        )?;
        clauses.push((canonical_id, dag_clause));
        mappings.push(ClauseTraceOriginalMapping {
            canonical_id,
            trace_index,
            trace_entry: ClauseTraceEntry::new(entry.id, mapped_clause, true, Vec::new()),
        });
    }
    let expected_first_derived = u64::try_from(shape.original_clauses)
        .map_err(|_| ClauseTraceResolutionError::CanonicalIdOverflow)?
        .checked_add(1)
        .ok_or(ClauseTraceResolutionError::CanonicalIdOverflow)?;
    debug_assert_eq!(next_canonical_id, expected_first_derived);
    Ok(OriginalConversion {
        clauses,
        mappings,
        next_canonical_id,
    })
}

include!("validation_finalize.rs");
include!("derived_conversion.rs");
