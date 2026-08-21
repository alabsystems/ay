// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Conversion-scoped root-propagation state for cheap per-row chain repair.
///
/// The recorded chains this converter repairs omit ROOT-LEVEL antecedents:
/// facts the producer's solver held at decision level zero, whose reason
/// chains conflict analysis therefore never walked. Those facts are implied
/// by the original clauses (plus the fixed premises) outright, independent
/// of any row's negated target — so their derivations are computed ONCE, by
/// a single unit-propagation fixpoint with recorded reasons, and reused by
/// every row instead of re-sweeping the whole database per row (which made
/// repair cost `rows x database` and exhausted the deterministic work
/// budget on real traces).
struct RootPropagation {
    /// Root-implied assignment (fixed premises included).
    assign: Vec<Option<bool>>,
    /// Canonical id that propagated each variable (0 = premise/unassigned).
    reason: Vec<u64>,
    /// 1-based position of each variable in root propagation order
    /// (0 = not propagated).
    order_pos: Vec<u32>,
    /// The database conflicts outright under the fixed premises: every row
    /// is derivable by this clause's root cone alone.
    conflict: Option<u64>,
    /// The fixed premise set contradicts itself; replay's own fixed-premise
    /// conflict rule makes the empty chain a complete derivation.
    premises_conflict: bool,
    /// Per-row scratch, reused across rows: this row's reason per variable
    /// (0 = none this row), row assignment trail (which doubles as the
    /// propagation queue), row propagation order, cone marks (1 = root cone,
    /// 2 = row cone) and the list of marked variables for O(cone) clearing,
    /// and the cone walk stack.
    cand_reason: Vec<u64>,
    row_trail: Vec<u32>,
    cand_order: Vec<u32>,
    cone_mark: Vec<u8>,
    cone_vars: Vec<u32>,
    cone_stack: Vec<u32>,
    /// Literal-keyed occurrence index over the ORIGINAL canonical clauses
    /// (CSR: `heads[code]..heads[code + 1]` are 0-based clause positions
    /// whose clause contains the literal with that code). Scanning the
    /// bucket of a literal the row's propagation just falsified visits
    /// exactly the original clauses that can newly become unit, so per-row
    /// repair costs the propagation cascade instead of a database sweep.
    /// `None` when the namespace exceeds the `u32` build guard.
    index_heads: Option<Vec<u32>>,
    index_items: Vec<u32>,
}

/// Occurrence-index code of a literal: `2 * var + polarity`.
fn literal_code(variable: usize, positive: bool) -> usize {
    variable * 2 + usize::from(positive)
}

/// Build the root-propagation state: seed the fixed premises, then propagate
/// the original clauses to a deterministic fixpoint, recording each
/// propagated variable's reason id and order.
fn compute_root_propagation(
    original_clauses: &[(u64, Vec<Literal>)],
    fixed_unit_premises: &[Literal],
    num_vars: usize,
    meter: &mut ConversionMeter<'_>,
) -> Result<RootPropagation, ResolutionValidationError> {
    let mut root = RootPropagation {
        assign: Vec::new(),
        reason: Vec::new(),
        order_pos: Vec::new(),
        conflict: None,
        premises_conflict: false,
        cand_reason: Vec::new(),
        row_trail: Vec::new(),
        cand_order: Vec::new(),
        cone_mark: Vec::new(),
        cone_vars: Vec::new(),
        cone_stack: Vec::new(),
        index_heads: None,
        index_items: Vec::new(),
    };
    reserve_root_propagation_buffers(&mut root, num_vars, meter)?;

    if seed_root_premises(&mut root, fixed_unit_premises, num_vars, meter)? {
        return Ok(root);
    }

    propagate_root_clauses(&mut root, original_clauses, meter)?;
    if root.conflict.is_some() {
        return Ok(root);
    }

    build_root_occurrence_index(&mut root, original_clauses, num_vars, meter)?;
    Ok(root)
}

/// Canonical id -> clause lookup over the exact prior database, shared by
/// the repair lanes. Ids the lanes look up are ids the same conversion
/// produced, so a miss is unreachable; it is still handled rather than
/// trusted.
fn prior_clause_by_id<'db>(
    original_clauses: &'db [(u64, Vec<Literal>)],
    derived: &'db [RupStep],
    id: u64,
) -> Option<&'db [Literal]> {
    let index = id
        .checked_sub(1)
        .and_then(|value| usize::try_from(value).ok())?;
    if let Some((stored_id, clause)) = original_clauses.get(index) {
        return (*stored_id == id).then_some(clause.as_slice());
    }
    let derived_index = index.checked_sub(original_clauses.len())?;
    let step = derived.get(derived_index)?;
    (step.id == id).then_some(step.clause.as_slice())
}

/// Mark and collect the ROOT cone supporting `seed_clause`: every variable
/// whose root reason transitively feeds a literal of the seed. Marked
/// variables land in `cone_vars` with mark 1; the caller clears both.
fn mark_root_cone_for_clause(
    root: &mut RootPropagation,
    original_clauses: &[(u64, Vec<Literal>)],
    seed_clause: &[Literal],
    meter: &mut ConversionMeter<'_>,
) -> Result<(), ResolutionValidationError> {
    debug_assert!(root.cone_stack.is_empty());
    for &literal in seed_clause {
        meter.charge(1)?;
        let variable = literal.variable().index();
        if root.reason[variable] != 0 && root.cone_mark[variable] == 0 {
            root.cone_mark[variable] = 1;
            root.cone_vars.push(variable as u32);
            root.cone_stack.push(variable as u32);
        }
    }
    while let Some(variable) = root.cone_stack.pop() {
        meter.charge(1)?;
        let reason_id = root.reason[variable as usize];
        // Root reasons are original-clause ids by construction.
        let Some(reason_clause) = prior_clause_by_id(original_clauses, &[], reason_id) else {
            continue;
        };
        for &literal in reason_clause {
            meter.charge(1)?;
            let support = literal.variable().index();
            if support != variable as usize
                && root.reason[support] != 0
                && root.cone_mark[support] == 0
            {
                root.cone_mark[support] = 1;
                root.cone_vars.push(support as u32);
                root.cone_stack.push(support as u32);
            }
        }
    }
    Ok(())
}

fn reserve_root_propagation_buffers(
    root: &mut RootPropagation,
    num_vars: usize,
    meter: &mut ConversionMeter<'_>,
) -> Result<(), ResolutionValidationError> {
    for buffer_bytes in [
        size_of::<Option<bool>>(), // assign
        size_of::<u64>(),          // reason
        size_of::<u32>(),          // order_pos
        size_of::<u64>(),          // cand_reason
        size_of::<u32>(),          // row_trail
        size_of::<u32>(),          // cand_order
        size_of::<u8>(),           // cone_mark
        size_of::<u32>(),          // cone_vars
        size_of::<u32>(),          // cone_stack
    ] {
        // One accounting charge per reserved buffer; the byte envelope for
        // all of them is the planner's propagation-scratch term.
        meter.charge(buffer_bytes)?;
    }
    reserve_exact(
        &mut root.assign,
        num_vars,
        ResolutionValidationResource::AssignmentScratch,
        meter,
    )?;
    reserve_exact(
        &mut root.reason,
        num_vars,
        ResolutionValidationResource::AssignmentScratch,
        meter,
    )?;
    reserve_exact(
        &mut root.order_pos,
        num_vars,
        ResolutionValidationResource::AssignmentScratch,
        meter,
    )?;
    reserve_exact(
        &mut root.cand_reason,
        num_vars,
        ResolutionValidationResource::AssignmentScratch,
        meter,
    )?;
    reserve_exact(
        &mut root.row_trail,
        num_vars,
        ResolutionValidationResource::AssignmentScratch,
        meter,
    )?;
    reserve_exact(
        &mut root.cand_order,
        num_vars,
        ResolutionValidationResource::AssignmentScratch,
        meter,
    )?;
    reserve_exact(
        &mut root.cone_mark,
        num_vars,
        ResolutionValidationResource::AssignmentScratch,
        meter,
    )?;
    reserve_exact(
        &mut root.cone_vars,
        num_vars,
        ResolutionValidationResource::AssignmentScratch,
        meter,
    )?;
    reserve_exact(
        &mut root.cone_stack,
        num_vars,
        ResolutionValidationResource::AssignmentScratch,
        meter,
    )?;
    let mut filled = 0usize;
    while filled < num_vars {
        let chunk = (num_vars - filled).min(CONTROL_POLL_INTERVAL);
        meter.charge(chunk)?;
        filled += chunk;
        root.assign.resize(filled, None);
        root.reason.resize(filled, 0);
        root.order_pos.resize(filled, 0);
        root.cand_reason.resize(filled, 0);
        root.cone_mark.resize(filled, 0);
        meter.check_controls()?;
    }
    Ok(())
}

fn seed_root_premises(
    root: &mut RootPropagation,
    fixed_unit_premises: &[Literal],
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
        match root.assign[variable] {
            None => root.assign[variable] = Some(value),
            Some(existing) if existing == value => {}
            Some(_) => {
                root.premises_conflict = true;
                return Ok(true);
            }
        }
    }
    Ok(false)
}

fn propagate_root_clauses(
    root: &mut RootPropagation,
    original_clauses: &[(u64, Vec<Literal>)],
    meter: &mut ConversionMeter<'_>,
) -> Result<(), ResolutionValidationError> {
    let mut next_order = 1u32;
    'fixpoint: loop {
        meter.check_controls()?;
        let mut propagated = false;
        for (id, clause) in original_clauses
            .iter()
            .map(|(id, clause)| (*id, clause.as_slice()))
        {
            match scan_terminal_hint_clause(clause, &root.assign, meter)? {
                TerminalHintScan::Satisfied | TerminalHintScan::Open => {}
                TerminalHintScan::Unit(literal) => {
                    let variable = literal.variable().index();
                    meter.charge(1)?;
                    root.reason[variable] = id;
                    root.order_pos[variable] = next_order;
                    next_order = next_order.saturating_add(1);
                    root.assign[variable] = Some(literal.is_positive());
                    propagated = true;
                }
                TerminalHintScan::Conflict => {
                    root.conflict = Some(id);
                    return Ok(());
                }
            }
        }
        if !propagated {
            break 'fixpoint;
        }
    }
    Ok(())
}

/// Restore the root state's per-row invariants unconditionally. Every entry
/// point that mutates per-row scratch runs this on ALL exits (including `?`
/// failures) via [`compact_rup_hint_candidates_rooted`]'s single-exit shape.
fn rooted_repair_cleanup(root: &mut RootPropagation) {
    while let Some(variable) = root.row_trail.pop() {
        root.assign[variable as usize] = None;
        root.cand_reason[variable as usize] = 0;
    }
    root.cand_order.clear();
    while let Some(variable) = root.cone_vars.pop() {
        root.cone_mark[variable as usize] = 0;
    }
    root.cone_stack.clear();
}

fn build_root_occurrence_index(
    root: &mut RootPropagation,
    original_clauses: &[(u64, Vec<Literal>)],
    num_vars: usize,
    meter: &mut ConversionMeter<'_>,
) -> Result<(), ResolutionValidationError> {
    // Build the literal-keyed occurrence index over the originals (two-pass
    // CSR). Skipped — leaving the index `None` and the per-row lane to its
    // candidate passes plus the full-sweep fallback — when the namespace
    // exceeds the u32 build guard.
    let total_literals: usize = original_clauses.iter().map(|(_, c)| c.len()).sum();
    let code_count = num_vars.checked_mul(2).and_then(|n| n.checked_add(1));
    if let Some(code_count) = code_count {
        if u32::try_from(total_literals).is_ok() && u32::try_from(original_clauses.len()).is_ok() {
            let mut heads: Vec<u32> = Vec::new();
            reserve_exact(
                &mut heads,
                code_count,
                ResolutionValidationResource::AssignmentScratch,
                meter,
            )?;
            let mut filled = 0usize;
            while filled < code_count {
                let chunk = (code_count - filled).min(CONTROL_POLL_INTERVAL);
                meter.charge(chunk)?;
                filled += chunk;
                heads.resize(filled, 0);
            }
            for (_, clause) in original_clauses {
                for &literal in clause {
                    meter.charge(1)?;
                    heads[literal_code(literal.variable().index(), literal.is_positive())] += 1;
                }
            }
            let mut running = 0u32;
            for head in heads.iter_mut() {
                meter.charge(1)?;
                let count = *head;
                *head = running;
                running = running.saturating_add(count);
            }
            let mut items: Vec<u32> = Vec::new();
            reserve_exact(
                &mut items,
                total_literals,
                ResolutionValidationResource::AssignmentScratch,
                meter,
            )?;
            let mut fill = 0usize;
            while fill < total_literals {
                let chunk = (total_literals - fill).min(CONTROL_POLL_INTERVAL);
                meter.charge(chunk)?;
                fill += chunk;
                items.resize(fill, 0);
            }
            let mut cursor: Vec<u32> = Vec::new();
            reserve_exact(
                &mut cursor,
                heads.len(),
                ResolutionValidationResource::AssignmentScratch,
                meter,
            )?;
            meter.charge(heads.len())?;
            cursor.extend_from_slice(&heads);
            for (position, (_, clause)) in original_clauses.iter().enumerate() {
                for &literal in clause {
                    meter.charge(1)?;
                    let code = literal_code(literal.variable().index(), literal.is_positive());
                    items[cursor[code] as usize] = position as u32;
                    cursor[code] += 1;
                }
            }
            // After the prefix sum, `heads[code]..heads[code + 1]` is the
            // bucket of `code` (codes occupy 0..2 * num_vars, and the extra
            // trailing slot holds the total as the sentinel).
            root.index_heads = Some(heads);
            root.index_items = items;
        }
    }
    Ok(())
}
