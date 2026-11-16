// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Repair one row's chain from the precomputed root propagation plus the
/// row's own recorded candidates: seed the root facts and the negated
/// target, propagate ONLY the candidate clauses to fixpoint, and on conflict
/// emit the combined cone — root-cone reasons in root propagation order,
/// then candidate-cone ids in candidate propagation order, then the
/// conflicting id. Repeated passes keep candidate order, but clauses already
/// satisfied in this row no longer need literal scans. `None` falls through
/// to the full-sweep synthesis.
fn compact_rup_hint_candidates_rooted(
    root: &mut RootPropagation,
    original_clauses: &[(u64, Vec<Literal>)],
    derived: &[RupStep],
    target_clause: &[Literal],
    candidate_hints: &[u64],
    max_hints: usize,
    admitted_recorded_capacity: usize,
    admitted_scheduler_bytes: usize,
    meter: &mut ConversionMeter<'_>,
) -> Result<Option<Vec<u64>>, ResolutionValidationError> {
    let result = rooted_repair_core(
        root,
        original_clauses,
        derived,
        target_clause,
        candidate_hints,
        max_hints,
        admitted_recorded_capacity,
        admitted_scheduler_bytes,
        meter,
    );
    rooted_repair_cleanup(root);
    result
}

fn rooted_repair_core(
    root: &mut RootPropagation,
    original_clauses: &[(u64, Vec<Literal>)],
    derived: &[RupStep],
    target_clause: &[Literal],
    candidate_hints: &[u64],
    max_hints: usize,
    admitted_recorded_capacity: usize,
    admitted_scheduler_bytes: usize,
    meter: &mut ConversionMeter<'_>,
) -> Result<Option<Vec<u64>>, ResolutionValidationError> {
    if root.premises_conflict {
        // Replay's own fixed-premise conflict rule derives every row.
        return Ok(Some(Vec::new()));
    }
    // Ordered chain assembly: (sort key, id). Root-cone entries key on root
    // propagation order; candidate entries are appended after sorting.
    let mut ordered: Vec<(u32, u64)> = Vec::new();

    match seed_rooted_target(root, target_clause, meter)? {
        RootSeedOutcome::Continue => {}
        RootSeedOutcome::Derived => return Ok(Some(Vec::new())),
        RootSeedOutcome::Synthesize => return Ok(None),
    }

    if let Some(conflict_id) = root.conflict {
        // The database conflicts outright under the premises: the root cone
        // of that clause derives ANY row (the target above agrees with every
        // root fact it shares a variable with).
        let Some(conflict_clause) = prior_clause_by_id(original_clauses, &[], conflict_id) else {
            return Ok(None);
        };
        mark_root_cone_for_clause(root, original_clauses, conflict_clause, meter)?;
        return finish_rooted_chain(root, &mut ordered, conflict_id, max_hints, meter);
    }

    let Some(conflict_id) = sweep_rooted_candidates(
        root,
        original_clauses,
        derived,
        candidate_hints,
        admitted_recorded_capacity,
        admitted_scheduler_bytes,
        meter,
    )?
    else {
        return Ok(None);
    };

    finish_combined_rooted_chain(
        root,
        original_clauses,
        derived,
        conflict_id,
        &mut ordered,
        max_hints,
        meter,
    )
}

/// Classify one cone support during the combined walk (candidate reasons
/// take precedence; a variable has exactly one of the two).
fn mark_combined_cone_var(root: &mut RootPropagation, variable: usize) {
    if root.cone_mark[variable] != 0 {
        return;
    }
    if root.cand_reason[variable] != 0 {
        root.cone_mark[variable] = 2;
    } else if root.reason[variable] != 0 {
        root.cone_mark[variable] = 1;
    } else {
        return;
    }
    root.cone_vars.push(variable as u32);
    root.cone_stack.push(variable as u32);
}

/// Emit a marked ROOT-only cone plus one terminal conflicting id.
fn finish_rooted_chain(
    root: &mut RootPropagation,
    ordered: &mut Vec<(u32, u64)>,
    conflict_id: u64,
    max_hints: usize,
    meter: &mut ConversionMeter<'_>,
) -> Result<Option<Vec<u64>>, ResolutionValidationError> {
    for &variable in &root.cone_vars {
        meter.charge(1)?;
        ordered.push((
            root.order_pos[variable as usize],
            root.reason[variable as usize],
        ));
    }
    ordered.sort_unstable();
    let chain_len = ordered.len() + 1;
    if chain_len > max_hints {
        return Ok(None);
    }
    let mut chain = Vec::new();
    reserve_exact(
        &mut chain,
        chain_len,
        ResolutionValidationResource::Hints,
        meter,
    )?;
    for &(_, id) in ordered.iter() {
        meter.charge(1)?;
        chain.push(id);
    }
    chain.push(conflict_id);
    Ok(Some(chain))
}

enum RootSeedOutcome {
    Continue,
    Derived,
    Synthesize,
}

fn seed_rooted_target(
    root: &mut RootPropagation,
    target_clause: &[Literal],
    meter: &mut ConversionMeter<'_>,
) -> Result<RootSeedOutcome, ResolutionValidationError> {
    let num_vars = root.assign.len();
    // Seed the negated target over the root facts FIRST: a target literal
    // contradicting a root-implied fact can satisfy reason clauses inside a
    // root cone under the actual replay assignment, so every rooted chain
    // below is only emitted when the target AGREES with each root fact it
    // touches. Contradictions punt to the full-sweep synthesis, whose own
    // propagation runs under the complete target assignment.
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
        let forced = !literal.is_positive();
        match root.assign[variable] {
            None => {
                root.assign[variable] = Some(forced);
                root.row_trail.push(variable as u32);
            }
            Some(existing) if existing == forced => {}
            Some(_) => {
                if root.reason[variable] == 0 && !root.row_trail.contains(&(variable as u32)) {
                    // Contradicts a fixed premise: replay's premise seeding
                    // hits the same conflict, so the empty chain derives the
                    // row.
                    return Ok(RootSeedOutcome::Derived);
                }
                if root.row_trail.contains(&(variable as u32)) {
                    // Contradicts an earlier literal of the same target: the
                    // row is a tautology, accepted by replay's own
                    // target-negation seeding with no hints.
                    return Ok(RootSeedOutcome::Derived);
                }
                // Contradicts a root-propagated fact: punt to synthesis.
                return Ok(RootSeedOutcome::Synthesize);
            }
        }
    }
    Ok(RootSeedOutcome::Continue)
}

fn sweep_rooted_candidates(
    root: &mut RootPropagation,
    original_clauses: &[(u64, Vec<Literal>)],
    derived: &[RupStep],
    candidate_hints: &[u64],
    admitted_recorded_capacity: usize,
    admitted_scheduler_bytes: usize,
    meter: &mut ConversionMeter<'_>,
) -> Result<Option<u64>, ResolutionValidationError> {
    // Row fixpoint over the combined assignment, in two escalating phases.
    // Phase 1 passes only over the row's recorded candidates: with the root
    // facts pre-seeded, most under-recorded rows conflict right away at
    // O(candidates) cost. Only when that stalls does phase 2 enable the
    // index-driven cascade over the original clauses whose literals this
    // row's propagation falsified (the row trail doubles as its queue),
    // still interleaved with candidate passes for the learned antecedents
    // the occurrence index does not cover.
    // Ordinary compaction's recorded flags are already dropped. This vector
    // reuses only that preflighted byte/header slot, not root propagation's
    // per-variable envelope or the widening slack. It lives for one sweep:
    // row cleanup may retract assignments, so flags must never cross rows.
    let mut retired = rooted_retirement::RetiredCandidates::new(
        candidate_hints.len(),
        admitted_recorded_capacity,
        meter,
    )?;
    let index_absent = root.index_heads.is_none();
    let mut use_index = false;
    let mut queue_cursor = 0usize;
    let mut first_pass = true;
    let mut schedule = rooted_scheduler::CandidateSchedule::Pending;
    let conflict_id = 'sweep: loop {
        meter.check_controls()?;
        {
            let RootPropagation {
                assign,
                cand_reason,
                row_trail,
                cand_order,
                index_heads,
                index_items,
                index_retired,
                ..
            } = &mut *root;
            if let Some(heads) = index_heads.as_ref().filter(|_| use_index) {
                while queue_cursor < row_trail.len() {
                    let variable = row_trail[queue_cursor] as usize;
                    queue_cursor += 1;
                    meter.charge(1)?;
                    let Some(assigned) = assign[variable] else {
                        continue;
                    };
                    let code = literal_code(variable, !assigned);
                    let start = heads[code] as usize;
                    let end = heads[code + 1] as usize;
                    for &item in &index_items[start..end] {
                        meter.charge(1)?;
                        let id = u64::from(item) + 1;
                        let Some(clause) = prior_clause_by_id(original_clauses, derived, id) else {
                            continue;
                        };
                        if index_retired.contains(item as usize, meter)? {
                            continue;
                        }
                        match scan_terminal_hint_clause(clause, assign, meter)? {
                            TerminalHintScan::Satisfied => {
                                index_retired.mark(item as usize, meter)?
                            }
                            TerminalHintScan::Open => {}
                            TerminalHintScan::Unit(literal) => {
                                let unit_var = literal.variable().index();
                                meter.charge(1)?;
                                assign[unit_var] = Some(literal.is_positive());
                                cand_reason[unit_var] = id;
                                row_trail.push(unit_var as u32);
                                cand_order.push(unit_var as u32);
                                index_retired.mark(item as usize, meter)?;
                            }
                            TerminalHintScan::Conflict => break 'sweep id,
                        }
                    }
                }
            }
        }
        // Preserve the cheap first pass, and let the original CSR find an
        // immediate phase-2 conflict before allocating any candidate index.
        if !first_pass
            && !candidate_hints.is_empty()
            && matches!(schedule, rooted_scheduler::CandidateSchedule::Pending)
        {
            let Some(selected) = rooted_scheduler::CandidateSchedule::select(
                root,
                original_clauses,
                derived,
                candidate_hints,
                &retired,
                admitted_scheduler_bytes,
                meter,
            )?
            else {
                return Ok(None);
            };
            schedule = selected;
        }
        if let Some(ready) = schedule.indexed() {
            // Original-clause propagation still runs only at round start.
            // Notify its completed cascade, never interleave the two queues.
            ready.notify(root, None, &retired, meter)?;
        }
        let mut propagated = false;
        let mut position_cursor = 0usize;
        loop {
            if matches!(schedule, rooted_scheduler::CandidateSchedule::Exhausted) {
                break;
            }
            let position = if let Some(ready) = schedule.indexed() {
                let Some(position) = ready.pop(meter)? else {
                    break;
                };
                position
            } else {
                if position_cursor == candidate_hints.len() {
                    break;
                }
                let position = position_cursor;
                position_cursor += 1;
                position
            };
            let id = candidate_hints[position];
            meter.charge(1)?;
            if retired.contains(position) {
                continue;
            }
            let Some(clause) = prior_clause_by_id(original_clauses, derived, id) else {
                return Ok(None);
            };
            match scan_terminal_hint_clause(clause, &root.assign, meter)? {
                TerminalHintScan::Satisfied => retired.mark(position, meter)?,
                TerminalHintScan::Open => {}
                TerminalHintScan::Unit(literal) => {
                    let variable = literal.variable().index();
                    meter.charge(1)?;
                    root.assign[variable] = Some(literal.is_positive());
                    root.cand_reason[variable] = id;
                    root.row_trail.push(variable as u32);
                    root.cand_order.push(variable as u32);
                    retired.mark(position, meter)?;
                    propagated = true;
                    if let Some(ready) = schedule.indexed() {
                        ready.notify(root, Some(position), &retired, meter)?;
                    }
                }
                TerminalHintScan::Conflict => break 'sweep id,
            }
        }
        first_pass = false;
        if let Some(ready) = schedule.indexed() {
            ready.next_round(meter)?;
        }
        if !propagated && (use_index || !index_absent) {
            if !use_index {
                // Candidates alone stalled: escalate to the index cascade,
                // re-sweeping the whole row trail accumulated so far.
                use_index = true;
                queue_cursor = 0;
                continue;
            }
            if queue_cursor >= root.row_trail.len() {
                return Ok(None);
            }
        } else if !propagated {
            return Ok(None);
        }
    };
    Ok(Some(conflict_id))
}

fn finish_combined_rooted_chain(
    root: &mut RootPropagation,
    original_clauses: &[(u64, Vec<Literal>)],
    derived: &[RupStep],
    conflict_id: u64,
    ordered: &mut Vec<(u32, u64)>,
    max_hints: usize,
    meter: &mut ConversionMeter<'_>,
) -> Result<Option<Vec<u64>>, ResolutionValidationError> {
    // Combined cone: classify each support as candidate-propagated (mark 2)
    // or root-propagated (mark 1); target/premise variables terminate.
    let Some(conflict_clause) = prior_clause_by_id(original_clauses, derived, conflict_id) else {
        return Ok(None);
    };
    debug_assert_eq!(root.cone_stack.len(), 0);
    for &literal in conflict_clause {
        meter.charge(1)?;
        let variable = literal.variable().index();
        mark_combined_cone_var(root, variable);
    }
    while let Some(variable) = root.cone_stack.pop() {
        meter.charge(1)?;
        let variable = variable as usize;
        let reason_id = if root.cone_mark[variable] == 2 {
            root.cand_reason[variable]
        } else {
            root.reason[variable]
        };
        let Some(reason_clause) = prior_clause_by_id(original_clauses, derived, reason_id) else {
            continue;
        };
        for &literal in reason_clause {
            meter.charge(1)?;
            let support = literal.variable().index();
            if support != variable {
                mark_combined_cone_var(root, support);
            }
        }
    }
    for &variable in &root.cone_vars {
        meter.charge(1)?;
        if root.cone_mark[variable as usize] == 1 {
            ordered.push((
                root.order_pos[variable as usize],
                root.reason[variable as usize],
            ));
        }
    }
    ordered.sort_unstable();
    let cand_in_cone = root
        .cand_order
        .iter()
        .filter(|&&variable| root.cone_mark[variable as usize] == 2)
        .count();
    let chain_len = ordered.len() + cand_in_cone + 1;
    if chain_len > max_hints {
        return Ok(None);
    }
    let mut chain = Vec::new();
    reserve_exact(
        &mut chain,
        chain_len,
        ResolutionValidationResource::Hints,
        meter,
    )?;
    for &(_, id) in ordered.iter() {
        meter.charge(1)?;
        chain.push(id);
    }
    for &variable in &root.cand_order {
        meter.charge(1)?;
        if root.cone_mark[variable as usize] == 2 {
            chain.push(root.cand_reason[variable as usize]);
        }
    }
    chain.push(conflict_id);
    Ok(Some(chain))
}
