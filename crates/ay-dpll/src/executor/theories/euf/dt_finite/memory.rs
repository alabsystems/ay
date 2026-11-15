// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Memory budget of the finite-domain datatype lane (#dt-fd-memory).
//!
//! The lane must never be what ends a check-sat in `memout`: whenever its
//! encoding or its solver would not fit, it declines and the fallback lanes
//! run. Two facts shape the budget.
//!
//! * The process ceiling that ends a run is the allocator's HARD ceiling
//!   (`ay_sys::arm_hard_memory_ceiling`), and it is enforced on LIVE heap
//!   bytes, which count reserved-but-untouched capacity. The advisory
//!   `process_memory_exceeded_at_percent` reads the physical footprint
//!   instead, which can sit far below the live count (measured: 3.4 MB
//!   footprint, 1.8 GB resident, on a run the ceiling then ended). Every
//!   check here therefore takes the LARGER of the two signals.
//! * Growth is bursty: a clause vector or a solver arena doubles in one
//!   allocation, which no poll between two clauses can see. So the clause
//!   count is capped up front from the room left under the ceiling, at the
//!   measured whole-lane peak per clause, and the polls are only backstops.

/// Peak bytes per clause of one whole round (encoding, solver load and the
/// first arena growth), with headroom. Measured: 196-200 bytes per clause of
/// peak resident memory on 9.3M-13.0M-clause encodings (`kprobe_3200`,
/// `kprobe_3500`, `kprobe_3800`, `b26_mem_g240_k4500_iscons`, verify-1
/// audit); a first learned-clause arena doubling adds about 64 more.
const PEAK_BYTES_PER_CLAUSE: usize = 320;
/// `ay-sat` bytes per original clause and per literal (arena, watches,
/// original-clause ledger), measured on the lane's own encodings.
const SOLVER_BYTES_PER_CLAUSE: usize = 64;
const SOLVER_BYTES_PER_LITERAL: usize = 24;
/// Share of the ceiling the encoding may grow to (polled backstop).
pub(super) const ENCODE_MEMORY_PERCENT: usize = 45;
/// Share of the ceiling the loaded solver and the clause cap may reach.
const LOAD_MEMORY_PERCENT: usize = 70;
/// Share at which the search stops (the advisory guard trips at 95%).
const SOLVE_MEMORY_PERCENT: usize = 90;

/// Bytes in use, as the larger of the live heap count (what the hard
/// ceiling enforces) and the physical footprint.
fn bytes_in_use() -> usize {
    ay_sys::current_live_bytes().max(ay_sys::current_footprint_bytes())
}

/// Whether either memory signal is past `percent` of the ceiling.
fn share_exceeded(percent: usize) -> bool {
    ay_sys::process_memory_exceeded_at_percent(percent)
        || ay_sys::live_bytes_exceeded_at_percent(percent)
}

/// Whether the encoding has outgrown its share (a backstop to the cap).
pub(super) fn encode_memory_exceeded() -> bool {
    share_exceeded(ENCODE_MEMORY_PERCENT)
}

/// Whether the search should stop short of the ceiling.
pub(super) fn solve_memory_exceeded() -> bool {
    share_exceeded(SOLVE_MEMORY_PERCENT)
}

/// The clause cap of one round: `max`, lowered to what the room left under
/// [`LOAD_MEMORY_PERCENT`] of the ceiling holds at [`PEAK_BYTES_PER_CLAUSE`].
/// `max` when no ceiling is set.
pub(super) fn clause_budget(max: usize) -> usize {
    budget_for(ay_sys::get_process_memory_limit(), bytes_in_use(), max)
}

/// [`clause_budget`] for a ceiling of `limit` bytes (0: none) with `used`
/// bytes in use.
pub(super) fn budget_for(limit: usize, used: usize, max: usize) -> usize {
    if limit == 0 {
        return max;
    }
    let room = (limit / 100 * LOAD_MEMORY_PERCENT).saturating_sub(used);
    (room / PEAK_BYTES_PER_CLAUSE).min(max)
}

/// Whether loading `clauses` clauses of `literals` literals into `ay-sat`
/// stays under [`LOAD_MEMORY_PERCENT`] of the ceiling. The solver reserves
/// its arena in one allocation, which the hard ceiling refuses outright, so
/// this is decided before loading.
pub(super) fn solver_fits(clauses: usize, literals: usize) -> bool {
    let limit = ay_sys::get_process_memory_limit();
    if limit == 0 {
        return true;
    }
    let need = clauses
        .saturating_mul(SOLVER_BYTES_PER_CLAUSE)
        .saturating_add(literals.saturating_mul(SOLVER_BYTES_PER_LITERAL));
    bytes_in_use().saturating_add(need) <= limit / 100 * LOAD_MEMORY_PERCENT
}
