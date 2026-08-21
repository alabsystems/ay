// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

fn preflight_trace_shape(
    trace: &ClauseTrace,
    entries: TraceEntries<'_>,
    num_vars: usize,
    additional_retained_bytes: usize,
    allow_synthesized_terminal: bool,
    meter: &mut ConversionMeter<'_>,
) -> Result<TraceShape, ResolutionValidationError> {
    meter.check_controls()?;
    let source_trace_bytes = retained_source_trace_bytes(trace)?;
    // Exact worst-case width of an independently reconstructed positive-RUP
    // chain: a deterministic unit-propagation run records at most one hint per
    // newly assigned variable plus one final conflicting clause, and can never
    // name more rows than precede it.
    let propagation_and_conflict_bound =
        checked_resource_add(num_vars, 1, ResolutionValidationResource::Hints)?;
    let reconstruction_row_bound = entries.len().min(propagation_and_conflict_bound);
    let (mut shape, mut widened_hints, has_derived_empty) =
        scan_trace_shape(entries, source_trace_bytes, reconstruction_row_bound, meter)?;

    // An assumption solve can finish from a conflict against a temporary
    // decision without adding a permanent empty clause to ClauseTrace. The
    // marker alone is never authority. Under exact fixed unit premises the
    // converter may reconstruct one terminal positive-RUP step, but its full
    // worst-case retained shape must be admitted before any conversion
    // allocation. A deterministic unit-propagation chain uses at most one hint
    // per newly assigned variable plus one final conflicting clause, and never
    // more hints than there are preceding clauses.
    account_synthesized_terminal(
        trace,
        allow_synthesized_terminal,
        has_derived_empty,
        reconstruction_row_bound,
        &mut shape,
        &mut widened_hints,
        meter,
    )?;

    let planned = choose_trace_plan(
        shape,
        widened_hints,
        entries.len(),
        num_vars,
        reconstruction_row_bound,
        additional_retained_bytes,
        meter.limits,
    )?;
    shape = planned.shape;
    let conversion_peak = planned.conversion;
    let replay_peak = planned.replay;
    enforce_resource(
        ResolutionValidationResource::Bytes,
        conversion_peak,
        meter.limits.max_bytes,
    )?;

    enforce_resource(
        ResolutionValidationResource::Bytes,
        replay_peak,
        meter.limits.max_bytes,
    )?;
    // Slack the conversion loop may spend widening individual reconstructed
    // chains past their admitted width (see the TraceShape field docs). Under
    // the widened plan every row is already admitted at full reconstruction
    // width, so the slack is simply never consumed there.
    shape.widening_hint_slack = meter.limits.max_hints.saturating_sub(shape.hints);
    shape.widening_byte_slack = meter
        .limits
        .max_bytes
        .saturating_sub(conversion_peak.max(replay_peak));
    meter.check_controls()?;
    Ok(shape)
}

fn retained_source_trace_bytes(trace: &ClauseTrace) -> Result<usize, ResolutionValidationError> {
    // Arena model (#A3): the trace retains one metadata vector plus two
    // shared pools; the retained-capacity census is those three allocations,
    // not a per-entry heap walk.
    let mut bytes = checked_resource_add(
        size_of::<ClauseTrace>(),
        checked_resource_mul(
            trace.entries_capacity(),
            ClauseTrace::entry_slot_bytes(),
            ResolutionValidationResource::Bytes,
        )?,
        ResolutionValidationResource::Bytes,
    )?;
    for (capacity, element_size) in [
        (trace.lit_pool_capacity(), size_of::<Literal>()),
        (trace.hint_pool_capacity(), size_of::<u64>()),
        (trace.scope_assumptions_capacity(), size_of::<Literal>()),
    ] {
        bytes = checked_resource_add(
            bytes,
            checked_resource_mul(capacity, element_size, ResolutionValidationResource::Bytes)?,
            ResolutionValidationResource::Bytes,
        )?;
    }
    Ok(bytes)
}

fn scan_trace_shape(
    entries: TraceEntries<'_>,
    source_trace_bytes: usize,
    reconstruction_row_bound: usize,
    meter: &mut ConversionMeter<'_>,
) -> Result<(TraceShape, Option<usize>, bool), ResolutionValidationError> {
    let mut shape = TraceShape {
        source_trace_bytes,
        ..TraceShape::default()
    };
    // `None` means the fully widened plan overflowed and is unavailable.
    let mut widened_hints: Option<usize> = Some(0);
    let mut has_derived_empty = false;
    for (entry_index, entry) in entries.iter().enumerate() {
        if entry_index % CONTROL_POLL_INTERVAL == 0 {
            meter.check_controls()?;
        }
        meter.charge(1)?;
        if entry.is_original {
            shape.original_clauses = add_count(
                shape.original_clauses,
                1,
                ResolutionValidationResource::OriginalClauses,
                meter.limits.max_original_clauses,
            )?;
            shape.original_literals = add_count(
                shape.original_literals,
                entry.clause.len(),
                ResolutionValidationResource::OriginalLiterals,
                meter.limits.max_original_literals,
            )?;
        } else {
            has_derived_empty |= entry.clause.is_empty();
            shape.derived_steps = add_count(
                shape.derived_steps,
                1,
                ResolutionValidationResource::DerivedSteps,
                meter.limits.max_derived_steps,
            )?;
            shape.derived_literals = add_count(
                shape.derived_literals,
                entry.clause.len(),
                ResolutionValidationResource::DerivedLiterals,
                meter.limits.max_derived_literals,
            )?;
            shape.hints = add_count(
                shape.hints,
                entry.resolution_hints.len(),
                ResolutionValidationResource::Hints,
                meter.limits.max_hints,
            )?;
            shape.max_row_hints = shape.max_row_hints.max(entry.resolution_hints.len());
            widened_hints = widened_hints.and_then(|total| {
                total.checked_add(entry.resolution_hints.len().max(reconstruction_row_bound))
            });
        }
        if entry.clause.len() >= CONTROL_POLL_INTERVAL
            || entry.resolution_hints.len() >= CONTROL_POLL_INTERVAL
        {
            meter.check_controls()?;
        }
    }
    Ok((shape, widened_hints, has_derived_empty))
}

fn account_synthesized_terminal(
    trace: &ClauseTrace,
    allow_synthesized_terminal: bool,
    has_derived_empty: bool,
    reconstruction_row_bound: usize,
    shape: &mut TraceShape,
    widened_hints: &mut Option<usize>,
    meter: &ConversionMeter<'_>,
) -> Result<(), ResolutionValidationError> {
    if !allow_synthesized_terminal || !trace.has_empty_clause() || has_derived_empty {
        return Ok(());
    }
    shape.synthesize_terminal_empty = true;
    shape.derived_steps = add_count(
        shape.derived_steps,
        1,
        ResolutionValidationResource::DerivedSteps,
        meter.limits.max_derived_steps,
    )?;
    shape.hints = add_count(
        shape.hints,
        reconstruction_row_bound,
        ResolutionValidationResource::Hints,
        meter.limits.max_hints,
    )?;
    shape.max_row_hints = shape.max_row_hints.max(reconstruction_row_bound);
    *widened_hints = widened_hints.and_then(|total| total.checked_add(reconstruction_row_bound));
    Ok(())
}

fn planned_trace_peaks(
    mut shape: TraceShape,
    num_vars: usize,
    reconstruction_row_bound: usize,
    additional_retained_bytes: usize,
    namespace_bytes: usize,
    assignment_bytes: usize,
) -> Result<PlannedPeaks, ResolutionValidationError> {
    // Reconstruction and its cone-trimmed output are bounded by one hint per
    // variable plus the conflict, including in the slack-funded plan.
    shape.synthesis_scratch_bytes = planned_synthesis_scratch_bytes(
        num_vars,
        shape.max_row_hints.max(reconstruction_row_bound),
    )?;
    let retained = planned_retained_bytes(shape, additional_retained_bytes)?;
    let conversion = checked_resource_add(
        checked_resource_add(
            retained,
            namespace_bytes,
            ResolutionValidationResource::Bytes,
        )?,
        shape.synthesis_scratch_bytes,
        ResolutionValidationResource::Bytes,
    )?;
    let replay = checked_resource_add(
        checked_resource_add(
            retained,
            namespace_bytes,
            ResolutionValidationResource::Bytes,
        )?,
        assignment_bytes,
        ResolutionValidationResource::Bytes,
    )?;
    Ok(PlannedPeaks {
        shape,
        conversion,
        replay,
    })
}

fn choose_trace_plan(
    shape: TraceShape,
    widened_hints: Option<usize>,
    entry_count: usize,
    num_vars: usize,
    reconstruction_row_bound: usize,
    additional_retained_bytes: usize,
    limits: &ResolutionValidationLimits,
) -> Result<PlannedPeaks, ResolutionValidationError> {
    // Hash tables reserve spare buckets to preserve their load factor. Budget
    // a checked 2x bucket envelope; actual capacity is checked after reserve.
    let namespace_bucket_bound =
        checked_resource_mul(entry_count, 2, ResolutionValidationResource::Bytes)?;
    let namespace_bytes = checked_resource_mul(
        namespace_bucket_bound,
        HASH_ENTRY_BYTES,
        ResolutionValidationResource::Bytes,
    )?;
    let assignment_bytes = checked_resource_mul(
        num_vars,
        checked_resource_add(
            size_of::<Option<bool>>(),
            size_of::<usize>(),
            ResolutionValidationResource::Bytes,
        )?,
        ResolutionValidationResource::Bytes,
    )?;
    let make_plan = |candidate| {
        planned_trace_peaks(
            candidate,
            num_vars,
            reconstruction_row_bound,
            additional_retained_bytes,
            namespace_bytes,
            assignment_bytes,
        )
    };
    let mut planned = make_plan(shape)?;
    if let Some(widened_total) = widened_hints.filter(|&total| total <= limits.max_hints) {
        let widened = make_plan(TraceShape {
            hints: widened_total,
            max_row_hints: shape.max_row_hints.max(reconstruction_row_bound),
            row_hint_budget: reconstruction_row_bound,
            ..shape
        });
        if let Ok(widened) = widened {
            if widened.conversion <= limits.max_bytes && widened.replay <= limits.max_bytes {
                planned = widened;
            }
        }
    }
    Ok(planned)
}
