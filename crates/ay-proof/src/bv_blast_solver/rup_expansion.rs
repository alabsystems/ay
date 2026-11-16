// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded RUP expansion with caller-owned polls and indexed long clauses.

use super::{
    lit_from_sat, BvSolvedExportError, Clause, Lit, Literal, Refutation, ResRule, ResolutionDag,
    ResolutionStep, RupExpansionLimits, RupStep,
};
use std::collections::BTreeSet;

mod membership;
mod meter;
#[cfg(test)]
mod tests;
use meter::{reserve_rup_map, reserve_rup_vec, try_reserve_rup_map, RupExpansionState};

/// Expand the solver's RUP DAG into a [`Refutation`] of binary resolutions.
///
/// Premise-id namespace (matching [`super::BvBlastProof::validate`]): ids `0..nclauses`
/// name input clauses; ids `>= nclauses` name resolution steps, in order. We map
/// each LRAT id (originals `1..=nclauses`, derived `> nclauses`) onto that space.
pub(super) fn expand_dag_to_resolution(
    dag: &ResolutionDag,
    clauses: &[Clause],
    limits: Option<RupExpansionLimits>,
) -> Result<Refutation, BvSolvedExportError> {
    expand_dag_to_resolution_with_cancellation(dag, clauses, limits, &mut || true)
}

pub(super) fn expand_dag_to_resolution_with_cancellation(
    dag: &ResolutionDag,
    clauses: &[Clause],
    limits: Option<RupExpansionLimits>,
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<Refutation, BvSolvedExportError> {
    let nclauses = clauses.len() as u32;

    let mut state = RupExpansionState::new(nclauses, limits, keep_going);
    state.check_deadline()?;

    // Both LRAT maps retain one entry per original or derived clause. Reserve
    // their complete bounded capacity before inserting anything, so HashMap
    // growth cannot escape the public byte envelope midway through expansion.
    let map_entries = dag
        .original_clauses
        .len()
        .checked_add(dag.derived.len())
        .ok_or_else(|| state.accounting_overflow("RUP expansion bytes"))?;
    let step_capacity = if let Some(limits) = limits {
        let mut total_hints = 0_usize;
        for rup in &dag.derived {
            state.charge_work(1)?;
            total_hints = total_hints
                .checked_add(rup.rup_hints.len())
                .ok_or_else(|| state.accounting_overflow("RUP expansion bytes"))?;
        }
        total_hints.min(limits.max_steps)
    } else {
        0
    };
    reserve_rup_map::<u64, u32>(&mut state, map_entries)?;
    reserve_rup_map::<u64, Vec<Lit>>(&mut state, map_entries)?;
    state.reserve_steps(step_capacity)?;

    // LRAT id → BvBlast premise id (the id usable as a ResolutionStep premise).
    // Originals: LRAT id `k` (1-based) → clause index `k-1`.
    // Derived: filled in as we emit the *final* step that produces each derived
    // clause (the last pairwise step of its RUP expansion).
    let mut lrat_to_premise: std::collections::HashMap<u64, u32> = std::collections::HashMap::new();
    try_reserve_rup_map(&mut lrat_to_premise, map_entries, &state)?;
    for (lrat_id, _lits) in &dag.original_clauses {
        state.charge_work(1)?;
        lrat_to_premise.insert(*lrat_id, (*lrat_id - 1) as u32);
    }
    // Original clause literals by LRAT id, for RUP replay.
    let mut lits_by_lrat: std::collections::HashMap<u64, Vec<Lit>> =
        std::collections::HashMap::new();
    try_reserve_rup_map(&mut lits_by_lrat, map_entries, &state)?;
    for (lrat_id, lits) in &dag.original_clauses {
        let copy = copy_sat_lits_bounded(lits, &mut state)?;
        lits_by_lrat.insert(*lrat_id, copy);
    }

    for rup in &dag.derived {
        state.check_deadline()?;
        let target = copy_sat_lits_bounded(&rup.clause, &mut state)?;
        let (final_premise_id, stronger) =
            expand_one_rup_step(rup, &target, &lits_by_lrat, &lrat_to_premise, &mut state)?;
        // Register this derived clause so later steps can cite it: the clause
        // the emitted resolutions derived, which is stronger than `target` only
        // when the LRAT step weakened it (`stronger_resolvent`).
        lrat_to_premise.insert(rup.id, final_premise_id);
        lits_by_lrat.insert(rup.id, stronger.unwrap_or(target));
    }

    state.check_deadline()?;
    Ok(Refutation { steps: state.steps })
}

fn copy_sat_lits_bounded(
    source: &[Literal],
    state: &mut RupExpansionState<'_>,
) -> Result<Vec<Lit>, BvSolvedExportError> {
    let mut out = reserve_rup_vec(source.len(), state, source.len())?;
    for lit in source {
        state.charge_work(1)?;
        out.push(lit_from_sat(lit));
    }
    Ok(out)
}

fn copy_lits_bounded(
    source: &[Lit],
    state: &mut RupExpansionState<'_>,
) -> Result<Vec<Lit>, BvSolvedExportError> {
    let mut out = reserve_rup_vec(source.len(), state, source.len())?;
    for &lit in source {
        state.charge_work(1)?;
        out.push(lit);
    }
    Ok(out)
}

/// Expand a single RUP step into binary resolutions and return the BvBlast
/// premise-id of the step that yields a clause contained in `target`, plus
/// that clause when it is strictly stronger than `target`.
///
/// Algorithm (standard RUP → resolution by reverse propagation):
///  1. Replay RUP: assume `¬target`, walk `rup_hints` in order; each hint is
///     unit and propagates one literal, the last hint conflicts. Record, per
///     hint, the unit literal it propagated.
///  2. Walk the *used* hints in reverse, starting from the conflicting clause,
///     resolving on each recorded unit literal whenever the running resolvent
///     contains its negation. Each resolution is one emitted [`ResolutionStep`].
fn expand_one_rup_step(
    rup: &RupStep,
    target: &[Lit],
    lits_by_lrat: &std::collections::HashMap<u64, Vec<Lit>>,
    lrat_to_premise: &std::collections::HashMap<u64, u32>,
    state: &mut RupExpansionState<'_>,
) -> Result<(u32, Option<Vec<Lit>>), BvSolvedExportError> {
    state.check_deadline()?;
    // ── 1. RUP replay to discover per-hint unit literals. ──
    // Trail value: var → assigned bool. Assume ¬target.
    let mut assign: std::collections::HashMap<u32, bool> = std::collections::HashMap::new();
    let assignment_entries = target
        .len()
        .checked_add(rup.rup_hints.len())
        .ok_or_else(|| state.accounting_overflow("RUP expansion bytes"))?;
    reserve_rup_map::<u32, bool>(state, assignment_entries)?;
    try_reserve_rup_map(&mut assign, assignment_entries, state)?;
    for l in target {
        state.charge_work(1)?;
        // ¬l is forced true under the assumption.
        assign.insert(l.var, l.neg); // if l = +v then ¬l forces v=false; if l=¬v forces v=true
    }
    // For each hint, the unit literal it adds (None for the final conflict).
    let mut hint_units: Vec<Option<Lit>> =
        reserve_rup_vec(rup.rup_hints.len(), state, rup.rup_hints.len())?;
    let mut conflict_at: Option<usize> = None;
    for (i, &h) in rup.rup_hints.iter().enumerate() {
        state.charge_work(1)?;
        let clause = lits_by_lrat
            .get(&h)
            .ok_or(BvSolvedExportError::RupExpansionFailed { id: rup.id })?;
        let mut unassigned_count = 0_usize;
        let mut unassigned_lit = None;
        let mut satisfied = false;
        for &lit in clause {
            state.charge_work(1)?;
            match assign.get(&lit.var) {
                Some(&val) => {
                    // literal true iff (val == !lit.neg) i.e. var assigned to lit's polarity
                    let lit_true = val != lit.neg;
                    if lit_true {
                        satisfied = true;
                        break;
                    }
                    // else falsified, skip
                }
                None => {
                    unassigned_count = unassigned_count.saturating_add(1);
                    unassigned_lit = Some(lit);
                }
            }
        }
        if satisfied {
            // Already-true hint: contributes nothing; record as no-op.
            hint_units.push(None);
            continue;
        }
        match unassigned_count {
            0 => {
                // Conflict: all literals falsified.
                hint_units.push(None);
                conflict_at = Some(i);
                break;
            }
            1 => {
                let u =
                    unassigned_lit.ok_or(BvSolvedExportError::RupExpansionFailed { id: rup.id })?;
                // propagate: assign var so that u becomes true.
                assign.insert(u.var, !u.neg);
                hint_units.push(Some(u));
            }
            _ => {
                // Non-unit hint under RUP: the proof is not a clean unit chain.
                return Err(BvSolvedExportError::RupExpansionFailed { id: rup.id });
            }
        }
    }
    let conflict_idx = conflict_at.ok_or(BvSolvedExportError::RupExpansionFailed { id: rup.id })?;

    // ── 2. Reverse-resolve from the conflicting clause. ──
    let conflict_hint = rup.rup_hints[conflict_idx];
    let conflict_clause = lits_by_lrat
        .get(&conflict_hint)
        .ok_or(BvSolvedExportError::RupExpansionFailed { id: rup.id })?;
    let mut resolvent = copy_lits_bounded(conflict_clause, state)?;
    let mut last_premise: u32 = *lrat_to_premise
        .get(&conflict_hint)
        .ok_or(BvSolvedExportError::RupExpansionFailed { id: rup.id })?;

    // Walk hints before the conflict, in reverse, resolving on their unit vars.
    for j in (0..conflict_idx).rev() {
        state.charge_work(1)?;
        let Some(unit) = hint_units[j] else {
            continue; // no-op / satisfied hint contributes nothing
        };
        // Resolve only if the resolvent currently contains ¬unit (the pivot).
        if !contains_lit_bounded(&resolvent, unit.negated(), state)? {
            continue;
        }
        let hint_id = rup.rup_hints[j];
        let hint_clause = lits_by_lrat
            .get(&hint_id)
            .ok_or(BvSolvedExportError::RupExpansionFailed { id: rup.id })?;
        let pivot = unit.var;
        let new_resolvent = resolve_pair(&resolvent, hint_clause, pivot, state)?
            .ok_or(BvSolvedExportError::RupExpansionFailed { id: rup.id })?;
        let hint_premise = *lrat_to_premise
            .get(&hint_id)
            .ok_or(BvSolvedExportError::RupExpansionFailed { id: rup.id })?;
        let step_id = state.next_step_id;
        state.next_step_id =
            state
                .next_step_id
                .checked_add(1)
                .ok_or(BvSolvedExportError::ResourceLimit {
                    resource: "resolution step id space",
                    limit: u32::MAX as usize,
                    actual: usize::MAX,
                })?;
        let step_clause = copy_lits_bounded(&new_resolvent, state)?;
        state.push_step(ResolutionStep {
            id: step_id,
            clause: step_clause,
            rule: ResRule::Resolution,
            premises: [last_premise, hint_premise],
            pivot,
        })?;
        let previous = std::mem::replace(&mut resolvent, new_resolvent);
        state.recycle_resolution_buffer(previous);
        last_premise = step_id;
    }

    // The reverse-resolution resolvent must lie inside the target clause. LRAT
    // may state a weaker clause than its hint chain proves; later replays then
    // cite the stronger resolvent (see `stronger_resolvent`).
    let stronger = stronger_resolvent(resolvent, target, rup.id, state)?;

    // If the RUP chain produced the target in zero resolutions (a single
    // conflicting clause that already equals the target — e.g. a unit derived
    // directly), `last_premise` already names a clause contained in target, but
    // it may be an *original clause* id rather than a fresh step. The downstream
    // validator needs the derived clause to be citable; if no step was emitted,
    // emit a trivial identity is impossible (resolution needs two premises), so
    // require at least one resolution. For our bit-blast obligations every
    // derived clause needs >= 1 resolution, so this is satisfied; guard anyway.
    Ok((last_premise, stronger))
}

/// The resolvent a RUP step's reverse resolution derived, when it is strictly
/// stronger than the clause the LRAT step states (`None` when they are equal).
///
/// LRAT lets a derived clause WEAKEN what its hint chain proves. ay-sat emits
/// one when `Solver::subsume` strengthens a clause against a subsumer it has
/// already strengthened earlier in the same round, so the subsumer's current
/// clause is a subset of the result. Measured on `bvmul(a, b) == bvmul(b, a)`
/// under the default-features-off ay-sat that `cargo test -p ay-proof` links:
/// clause 15436 states 7 literals, its conflicting hint 15178 holds 5 of them,
/// and `ay check lrat` answers `s VERIFIED` for the whole proof. Demanding set
/// equality refused that valid proof (`RupExpansionFailed { id: 15436 }`).
///
/// Every emitted step is still a genuine binary resolution, and a later hint
/// that is unit or conflicting under the stated clause stays unit or
/// conflicting under any subset of it, so the caller registers the stronger
/// clause for later replays; `BvBlastProof::validate` still re-checks every
/// step. A resolvent outside the stated clause is refused.
fn stronger_resolvent(
    resolvent: Vec<Lit>,
    target: &[Lit],
    id: u64,
    state: &mut RupExpansionState<'_>,
) -> Result<Option<Vec<Lit>>, BvSolvedExportError> {
    if clause_set_eq(&resolvent, target, state)? {
        return Ok(None);
    }
    if !clause_subset(&resolvent, target, state)? {
        return Err(BvSolvedExportError::RupExpansionFailed { id });
    }
    Ok(Some(resolvent))
}

/// Binary resolution of `a` and `b` on `pivot`, deduplicated; `None` if `pivot`
/// is not a clean opposite-polarity pivot or the resolvent is tautological.
fn resolve_pair(
    a: &[Lit],
    b: &[Lit],
    pivot: u32,
    state: &mut RupExpansionState<'_>,
) -> Result<Option<Vec<Lit>>, BvSolvedExportError> {
    if !state.is_bounded() {
        let a_pos = a.contains(&Lit::pos(pivot));
        let a_neg = a.contains(&Lit::neg(pivot));
        let b_pos = b.contains(&Lit::pos(pivot));
        let b_neg = b.contains(&Lit::neg(pivot));
        let valid = (a_pos && b_neg && !a_neg && !b_pos) || (a_neg && b_pos && !a_pos && !b_neg);
        if !valid {
            return Ok(None);
        }
        let mut out: Vec<Lit> = Vec::new();
        let mut seen: BTreeSet<Lit> = BTreeSet::new();
        for &lit in a.iter().chain(b.iter()) {
            if lit.var == pivot {
                continue;
            }
            if seen.contains(&lit.negated()) {
                return Ok(None);
            }
            if seen.insert(lit) {
                out.push(lit);
            }
        }
        return Ok(Some(out));
    }

    let a_pos = contains_lit_bounded(a, Lit::pos(pivot), state)?;
    let a_neg = contains_lit_bounded(a, Lit::neg(pivot), state)?;
    let b_pos = contains_lit_bounded(b, Lit::pos(pivot), state)?;
    let b_neg = contains_lit_bounded(b, Lit::neg(pivot), state)?;
    let valid = (a_pos && b_neg && !a_neg && !b_pos) || (a_neg && b_pos && !a_pos && !b_neg);
    if !valid {
        return Ok(None);
    }
    let capacity = a
        .len()
        .checked_add(b.len())
        .ok_or_else(|| state.accounting_overflow("expanded literals"))?;
    if capacity > membership::INDEX_THRESHOLD {
        return membership::resolve(a, b, pivot, capacity, state);
    }
    let mut out: Vec<Lit> = reserve_rup_vec(capacity, state, capacity)?;
    for &l in a.iter().chain(b.iter()) {
        state.charge_work(1)?;
        if l.var == pivot {
            continue;
        }
        if contains_lit_bounded(&out, l.negated(), state)? {
            return Ok(None); // tautology
        }
        if !contains_lit_bounded(&out, l, state)? {
            out.push(l);
        }
    }
    Ok(Some(out))
}

fn contains_lit_bounded(
    clause: &[Lit],
    needle: Lit,
    state: &mut RupExpansionState<'_>,
) -> Result<bool, BvSolvedExportError> {
    for &lit in clause {
        state.charge_work(1)?;
        if lit == needle {
            return Ok(true);
        }
    }
    Ok(false)
}

/// Whether every literal of `a` occurs, with its polarity, in `b`. Reached only
/// after the exact comparison failed, so it costs nothing on an ordinary step.
fn clause_subset(
    a: &[Lit],
    b: &[Lit],
    state: &mut RupExpansionState<'_>,
) -> Result<bool, BvSolvedExportError> {
    if !state.is_bounded() {
        let sb: BTreeSet<Lit> = b.iter().copied().collect();
        return Ok(a.iter().all(|lit| sb.contains(lit)));
    }
    if a.len().max(b.len()) > membership::INDEX_THRESHOLD {
        return membership::subset(a, b, state);
    }
    for &lit in a {
        if !contains_lit_bounded(b, lit, state)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn clause_set_eq(
    a: &[Lit],
    b: &[Lit],
    state: &mut RupExpansionState<'_>,
) -> Result<bool, BvSolvedExportError> {
    if !state.is_bounded() {
        let sa: BTreeSet<Lit> = a.iter().copied().collect();
        let sb: BTreeSet<Lit> = b.iter().copied().collect();
        return Ok(sa == sb);
    }
    if a.len().max(b.len()) > membership::INDEX_THRESHOLD {
        return membership::equal(a, b, state);
    }
    for &lit in a {
        if !contains_lit_bounded(b, lit, state)? {
            return Ok(false);
        }
    }
    for &lit in b {
        if !contains_lit_bounded(a, lit, state)? {
            return Ok(false);
        }
    }
    Ok(true)
}
