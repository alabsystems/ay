// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

struct ConversionPayload {
    num_vars: usize,
    original_clauses: Vec<(u64, Vec<Literal>)>,
    original_mappings: Vec<ClauseTraceOriginalMapping>,
    derived: Vec<RupStep>,
    empty_clause_id: u64,
    entry_states: HashMap<u64, TraceIdState>,
    retained_premise_bytes: usize,
    source_trace_bytes: usize,
}

struct FinalizedConversion {
    dag: ResolutionDag,
    original_mappings: Vec<ClauseTraceOriginalMapping>,
    retained_bytes: usize,
    replay_additional_bytes: usize,
}

fn finalize_converted_trace(
    payload: ConversionPayload,
    meter: &mut ConversionMeter<'_>,
) -> Result<FinalizedConversion, ResolutionValidationError> {
    let ConversionPayload {
        num_vars,
        original_clauses,
        original_mappings,
        derived,
        empty_clause_id,
        entry_states,
        retained_premise_bytes,
        source_trace_bytes,
    } = payload;
    let dag = ResolutionDag {
        num_vars,
        original_clauses,
        derived,
        empty_clause_id,
    };
    let mapping_bytes =
        retained_mapping_bytes(&original_mappings, original_mappings.capacity(), meter)?;
    let dag_bytes = retained_dag_bytes(&dag, meter)?;
    let retained_bytes = checked_resource_add(
        checked_resource_add(
            checked_resource_add(
                dag_bytes,
                mapping_bytes,
                ResolutionValidationResource::Bytes,
            )?,
            retained_premise_bytes,
            ResolutionValidationResource::Bytes,
        )?,
        source_trace_bytes,
        ResolutionValidationResource::Bytes,
    )?;
    let conversion_bytes = checked_resource_add(
        retained_bytes,
        checked_resource_mul(
            entry_states.capacity(),
            HASH_ENTRY_BYTES,
            ResolutionValidationResource::Bytes,
        )?,
        ResolutionValidationResource::Bytes,
    )?;
    enforce_resource(
        ResolutionValidationResource::Bytes,
        conversion_bytes,
        meter.limits.max_bytes,
    )?;
    meter.check_controls()?;
    drop(entry_states);
    let replay_additional_bytes = checked_resource_add(
        checked_resource_add(
            mapping_bytes,
            source_trace_bytes,
            ResolutionValidationResource::Bytes,
        )?,
        retained_premise_bytes,
        ResolutionValidationResource::Bytes,
    )?;
    Ok(FinalizedConversion {
        dag,
        original_mappings,
        retained_bytes,
        replay_additional_bytes,
    })
}

fn replay_converted_dag(
    dag: &ResolutionDag,
    limits: &ResolutionValidationLimits,
    unit_premises: &[Literal],
    replay_additional_bytes: usize,
    conversion_work: u64,
    should_stop: &mut dyn FnMut() -> bool,
) -> Result<u64, ResolutionValidationError> {
    dag.validate_with_limits_interruptible(
        limits,
        unit_premises,
        replay_additional_bytes,
        conversion_work,
        should_stop,
    )
}
