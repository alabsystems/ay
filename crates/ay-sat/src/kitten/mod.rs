// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kitten: miniature CDCL sub-solver for SAT sweeping.
//!
//! Self-contained CDCL solver for small local sub-problems (100-1000 clauses).
//! Used by the sweep module to find backbone literals and literal equivalences
//! by solving on clause neighborhoods (Cone of Influence).
//!
//! Key design properties (matching CaDiCaL `kitten.c`):
//! - VMTF decision heuristic (no EVSIDS — problems are too small)
//! - No restarts, no clause deletion (sub-problems are short-lived)
//! - Tick-based effort control
//! - External↔internal literal mapping for sparse variable sets
//! - `flip_literal()`: O(watchlist) model perturbation for cheap backbone check
//! - Clausal core extraction for proof support
//!
//! Reference: CaDiCaL `kitten.c` (2599 lines C), adapted to Rust idioms.

mod model;
mod search;
mod state;
mod storage;

#[cfg(test)]
#[path = "../kitten_tests.rs"]
mod tests;

const INVALID: u32 = u32::MAX;

const CORE_FLAG: u32 = 1;
const LEARNED_FLAG: u32 = 2;

/// Per-variable assignment record.
#[derive(Clone, Copy, Default)]
struct Var {
    level: u32,
    reason: u32,
}

/// VMTF queue link.
#[derive(Clone, Copy)]
struct Link {
    next: u32,
    prev: u32,
    stamp: u64,
}

impl Default for Link {
    fn default() -> Self {
        Self {
            next: INVALID,
            prev: INVALID,
            stamp: 0,
        }
    }
}

/// Miniature CDCL solver for local sub-problems (sweeping, definitions).
///
/// Self-contained: does NOT share data structures with the main Solver.
/// Designed for small clause sets with tick-based effort control.
/// No restarts, no clause deletion, VMTF-only decisions.
pub(crate) struct Kitten {
    // Variable/literal state
    num_internal_vars: usize,
    values: Vec<i8>,
    phases: Vec<u8>,
    rng_state: u64,
    vars: Vec<Var>,
    marks: Vec<i8>,

    // VMTF queue
    links: Vec<Link>,
    queue_first: u32,
    queue_last: u32,
    queue_search: u32,
    queue_stamp: u64,
    unassigned: u32,

    // Clause arena (flat Vec<u32>: [aux, size, flags, lit0, lit1, ...])
    clause_data: Vec<u32>,
    end_original: usize,

    // Watches: per-literal Vec of clause offsets
    watches: Vec<Vec<u32>>,

    // Trail
    trail: Vec<u32>,
    propagated: usize,

    // Solving state
    level: u32,
    status: i32, // 0=unknown, 10=SAT, 20=UNSAT
    inconsistent: u32,

    // External↔internal mapping
    ext_to_int: Vec<u32>, // external var idx → internal idx + 1 (0 = unmapped)
    int_to_ext: Vec<u32>, // internal idx → external var idx

    // Working buffers
    analyzed: Vec<u32>,
    assumptions: Vec<u32>,
    units: Vec<u32>,
    clause_buf: Vec<u32>,
    resolved: Vec<u32>,

    // Antecedent tracking (for clausal core)
    track_antecedents: bool,
    failed: Vec<bool>,
    failing: u32,
    core: Vec<u32>,

    // Effort control
    ticks: u64,
    ticks_limit: u64,

    // Stats
    conflicts: u64,
    decisions: u64,
    propagations: u64,
}
