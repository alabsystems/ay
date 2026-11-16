// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn exhausted(owner: &CountedAdmission) -> CountedAdmissionError {
    owner.refuse(CountedAdmissionError::StorageExhausted)
}

/// Keep the ordinary bounded-growth plan and its current+replacement peak.
/// Each real replacement allocation, initialized copy and retirement is paid
/// before use. No payload row is changed on a reservation failure.
pub(super) fn prepare(
    trace: &mut ClauseTrace,
    clause_len: usize,
    hints_len: usize,
    owner: &CountedAdmission,
) -> Result<()> {
    owner.admit(32, 0)?;
    let current = ArenaCapacities::current(trace);
    let required = ArenaCapacities::required_after_add(trace, clause_len, hints_len)
        .ok_or_else(|| exhausted(owner))?;
    let budget = trace
        .budget_bytes
        .checked_sub(trace.originals.bytes)
        .and_then(|n| n.checked_sub(trace.deletion_bytes()))
        .ok_or_else(|| exhausted(owner))?;
    let target = current
        .bounded_growth(required, budget)
        .ok_or_else(|| exhausted(owner))?;
    let meta = replacement(&trace.meta, current.entries, target.entries, owner)?;
    peak(trace, current, &meta, &None, &None, owner)?;
    let literals = replacement(&trace.lit_pool, current.literals, target.literals, owner)?;
    peak(trace, current, &meta, &literals, &None, owner)?;
    let hints = replacement(&trace.hint_pool, current.hints, target.hints, owner)?;
    peak(trace, current, &meta, &literals, &hints, owner)?;
    owner.check()?;
    trace.install_replacements((meta, literals, hints));
    Ok(())
}

fn replacement<T>(
    values: &[T],
    current: usize,
    target: usize,
    owner: &CountedAdmission,
) -> Result<Option<Vec<T>>> {
    owner.admit(1, 0)?;
    if current == target {
        return Ok(None);
    }
    // Copies and old/new buffer retirement are separate from allocation work.
    let work = values
        .len()
        .checked_add(current)
        .and_then(|n| n.checked_add(target))
        .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?;
    owner.admit(work, 0)?;
    let replacement = try_reserved_exact(owner, target)?;
    let excess = replacement.capacity().saturating_sub(target);
    let bytes = excess
        .checked_mul(size_of::<T>())
        .ok_or_else(|| exhausted(owner))?;
    owner.admit(excess, bytes)?;
    Ok(Some(replacement))
}

fn peak(
    trace: &ClauseTrace,
    current: ArenaCapacities,
    meta: &Option<Vec<EntryMeta>>,
    literals: &Option<Vec<Literal>>,
    hints: &Option<Vec<u64>>,
    owner: &CountedAdmission,
) -> Result<()> {
    owner.admit(8, 0)?;
    let replacements = ArenaCapacities {
        entries: meta.as_ref().map_or(0, Vec::capacity),
        literals: literals.as_ref().map_or(0, Vec::capacity),
        hints: hints.as_ref().map_or(0, Vec::capacity),
    };
    if current
        .peak_with_replacements(replacements)
        .and_then(|n| n.checked_add(trace.originals.bytes))
        .and_then(|n| n.checked_add(trace.deletion_bytes()))
        .is_none_or(|bytes| bytes > trace.budget_bytes)
    {
        return Err(exhausted(owner));
    }
    Ok(())
}
