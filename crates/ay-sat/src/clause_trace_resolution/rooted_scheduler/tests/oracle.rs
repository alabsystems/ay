// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

// Frozen pre-scheduler two-phase loop. Differential ordering oracle, not a
// substitute for independent ResolutionDag replay. No scheduler calls here.
use super::*;

pub(super) fn legacy_sweep(
    root: &mut RootPropagation,
    original_clauses: &[(u64, Vec<Literal>)],
    derived: &[RupStep],
    candidate_hints: &[u64],
    admitted_recorded_capacity: usize,
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
                        match scan_terminal_hint_clause(clause, assign, meter)? {
                            TerminalHintScan::Satisfied | TerminalHintScan::Open => {}
                            TerminalHintScan::Unit(literal) => {
                                let unit_var = literal.variable().index();
                                meter.charge(1)?;
                                assign[unit_var] = Some(literal.is_positive());
                                cand_reason[unit_var] = id;
                                row_trail.push(unit_var as u32);
                                cand_order.push(unit_var as u32);
                            }
                            TerminalHintScan::Conflict => break 'sweep id,
                        }
                    }
                }
            }
        }
        let mut propagated = false;
        for (position, &id) in candidate_hints.iter().enumerate() {
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
                }
                TerminalHintScan::Conflict => break 'sweep id,
            }
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
