// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked retained-capacity planning for the clause-trace arenas.

use std::mem::size_of;

use super::{ClauseTrace, EntryMeta};
use crate::literal::Literal;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct ArenaCapacities {
    pub(super) entries: usize,
    pub(super) literals: usize,
    pub(super) hints: usize,
}

impl ArenaCapacities {
    pub(super) fn current(trace: &ClauseTrace) -> Self {
        Self {
            entries: trace.meta.capacity(),
            literals: trace.lit_pool.capacity(),
            hints: trace.hint_pool.capacity(),
        }
    }

    pub(super) fn retained_bytes(self) -> Option<usize> {
        self.entries
            .checked_mul(size_of::<EntryMeta>())?
            .checked_add(self.literals.checked_mul(size_of::<Literal>())?)?
            .checked_add(self.hints.checked_mul(size_of::<u64>())?)
    }

    pub(super) fn peak_with_replacements(self, replacements: Self) -> Option<usize> {
        self.retained_bytes()?
            .checked_add(replacements.retained_bytes()?)
    }

    pub(super) fn replacements_for(self, target: Self) -> Self {
        Self {
            entries: if target.entries != self.entries {
                target.entries
            } else {
                0
            },
            literals: if target.literals != self.literals {
                target.literals
            } else {
                0
            },
            hints: if target.hints != self.hints {
                target.hints
            } else {
                0
            },
        }
    }

    pub(super) fn required_after_add(
        trace: &ClauseTrace,
        clause_len: usize,
        hints_len: usize,
    ) -> Option<Self> {
        Some(Self {
            entries: trace.meta.len().checked_add(1)?,
            literals: trace.lit_pool.len().checked_add(clause_len)?,
            hints: trace.hint_pool.len().checked_add(hints_len)?,
        })
    }

    pub(super) fn bounded_growth(self, required: Self, budget: usize) -> Option<Self> {
        let grow_entries = required.entries > self.entries;
        let grow_literals = required.literals > self.literals;
        let grow_hints = required.hints > self.hints;
        let minimum = Self {
            entries: if grow_entries { required.entries } else { 0 },
            literals: if grow_literals { required.literals } else { 0 },
            hints: if grow_hints { required.hints } else { 0 },
        };
        let minimum_peak = self.peak_with_replacements(minimum)?;
        if minimum_peak > budget {
            return None;
        }
        let desired = Self {
            entries: if grow_entries {
                growth_target(self.entries, required.entries)
            } else {
                self.entries
            },
            literals: if grow_literals {
                growth_target(self.literals, required.literals)
            } else {
                self.literals
            },
            hints: if grow_hints {
                growth_target(self.hints, required.hints)
            } else {
                self.hints
            },
        };
        if self
            .peak_with_replacements(self.replacements_for(desired))
            .is_some_and(|bytes| bytes <= budget)
        {
            return Some(desired);
        }

        let remaining = budget.checked_sub(minimum_peak)?;
        let entry_demand = if grow_entries {
            desired.entries.checked_sub(required.entries)?
        } else {
            0
        };
        let literal_demand = if grow_literals {
            desired.literals.checked_sub(required.literals)?
        } else {
            0
        };
        let hint_demand = if grow_hints {
            desired.hints.checked_sub(required.hints)?
        } else {
            0
        };
        let total_demand = demand_bytes(entry_demand, size_of::<EntryMeta>())
            .saturating_add(demand_bytes(literal_demand, size_of::<Literal>()))
            .saturating_add(demand_bytes(hint_demand, size_of::<u64>()));
        let target = Self {
            entries: if grow_entries {
                proportional_capacity(
                    required.entries,
                    entry_demand,
                    size_of::<EntryMeta>(),
                    remaining,
                    total_demand,
                )
            } else {
                self.entries
            },
            literals: if grow_literals {
                proportional_capacity(
                    required.literals,
                    literal_demand,
                    size_of::<Literal>(),
                    remaining,
                    total_demand,
                )
            } else {
                self.literals
            },
            hints: if grow_hints {
                proportional_capacity(
                    required.hints,
                    hint_demand,
                    size_of::<u64>(),
                    remaining,
                    total_demand,
                )
            } else {
                self.hints
            },
        };
        self.peak_with_replacements(self.replacements_for(target))
            .filter(|peak| *peak <= budget)
            .map(|_| target)
    }
}

fn growth_target(current: usize, required: usize) -> usize {
    current.saturating_mul(2).max(required)
}

fn demand_bytes(slots: usize, slot_bytes: usize) -> u128 {
    (slots as u128).saturating_mul(slot_bytes as u128)
}

fn proportional_capacity(
    required: usize,
    demanded_slots: usize,
    slot_bytes: usize,
    remaining_bytes: usize,
    total_demand_bytes: u128,
) -> usize {
    if total_demand_bytes == 0 {
        return required;
    }
    let demand = demand_bytes(demanded_slots, slot_bytes);
    let share_bytes = (remaining_bytes as u128).saturating_mul(demand) / total_demand_bytes;
    let shared_slots = usize::try_from(share_bytes / (slot_bytes as u128)).unwrap_or(usize::MAX);
    required.saturating_add(shared_slots.min(demanded_slots))
}
