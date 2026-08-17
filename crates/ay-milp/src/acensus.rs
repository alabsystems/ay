// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ALLOCATION CENSUS — a load-invariant instrument.
//!
//! Wall clock on a shared box is not evidence. Allocation COUNT is: it is a property of the
//! walk the solver takes, not of the machine it takes it on. This module holds the counters a
//! `#[global_allocator]` in an example binary bumps, plus a handful of named scopes so the
//! count can be attributed to a region of the search rather than to the process as a whole.
//!
//! Everything here is inert unless an example installs the counting allocator, and the scopes
//! are inert unless `the acensus knob` is set. Nothing in this module can change a verdict:
//! it only reads counters and adds to them.

use std::sync::atomic::{AtomicU64, Ordering};

/// Bumped by the counting allocator in `examples/alloc_census.rs`. Zero in every normal build.
pub static ALLOC_N: AtomicU64 = AtomicU64::new(0);
/// Bytes requested, same source.
pub static ALLOC_B: AtomicU64 = AtomicU64::new(0);
/// Frees, so a leak shows up as a gap rather than as a mystery.
pub static DEALLOC_N: AtomicU64 = AtomicU64::new(0);

/// Live allocation count, for scope arithmetic.
#[inline]
pub fn allocs() -> u64 {
    ALLOC_N.load(Ordering::Relaxed)
}

/// Live requested-bytes total.
#[inline]
pub fn alloc_bytes() -> u64 {
    ALLOC_B.load(Ordering::Relaxed)
}

/// Live free count.
#[inline]
pub fn deallocs() -> u64 {
    DEALLOC_N.load(Ordering::Relaxed)
}

/// Named regions. Kept small and fixed-size so a scope costs two relaxed loads and two adds.
#[derive(Clone, Copy)]
pub(crate) enum Region {
    /// One main-loop iteration, end to end (LP and nested sub-MIPs included).
    Body = 0,
    /// The node's own LP solve.
    Lp = 1,
    /// Branch selection + `push_children`.
    Branch = 2,
    /// The exact/rational bound path at the node.
    Bound = 3,
    /// Box materialisation + node-entry propagation, before the LP.
    Prep = 4,
}

#[cfg(feature = "acensus")]
pub(crate) const N_REGIONS: usize = 5;
#[cfg(feature = "acensus")]
const NAMES: [&str; N_REGIONS] = [
    "node-body",
    "node-lp",
    "node-branch",
    "node-bound",
    "node-prep",
];

#[cfg(feature = "acensus")]
static REG_N: [AtomicU64; N_REGIONS] = [const { AtomicU64::new(0) }; N_REGIONS];
#[cfg(feature = "acensus")]
static REG_B: [AtomicU64; N_REGIONS] = [const { AtomicU64::new(0) }; N_REGIONS];
#[cfg(feature = "acensus")]
static REG_ENTERS: [AtomicU64; N_REGIONS] = [const { AtomicU64::new(0) }; N_REGIONS];

#[cfg(feature = "acensus")]
/// Whether the scopes are armed. Read once and cached; the env is not consulted per node.
pub(crate) fn armed() -> bool {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| crate::tune::caller_flag(crate::tune::Knob::Acensus) == Some(true))
}

/// An RAII allocation-delta scope. Constructing it when disarmed does nothing measurable.
#[cfg(feature = "acensus")]
pub(crate) struct Scope {
    region: usize,
    n0: u64,
    b0: u64,
    on: bool,
}

#[cfg(feature = "acensus")]
impl Scope {
    #[inline]
    pub(crate) fn new(region: Region) -> Self {
        let on = armed();
        Self {
            region: region as usize,
            n0: if on { allocs() } else { 0 },
            b0: if on { alloc_bytes() } else { 0 },
            on,
        }
    }
}

#[cfg(feature = "acensus")]
impl Drop for Scope {
    #[inline]
    fn drop(&mut self) {
        if !self.on {
            return;
        }
        REG_N[self.region].fetch_add(allocs().wrapping_sub(self.n0), Ordering::Relaxed);
        REG_B[self.region].fetch_add(alloc_bytes().wrapping_sub(self.b0), Ordering::Relaxed);
        REG_ENTERS[self.region].fetch_add(1, Ordering::Relaxed);
    }
}

/// FEATURE OFF: a field-less unit with NO `Drop`, so the probe leaves not one instruction in
/// the node loop. This is why the census can live in the hot path at all — a disarmed runtime
/// branch would still be a branch, 18 of them a node, in the one loop that must not pay for
/// instrumentation.
#[cfg(not(feature = "acensus"))]
pub(crate) struct Scope;

#[cfg(not(feature = "acensus"))]
impl Scope {
    #[inline(always)]
    pub(crate) const fn new(_region: Region) -> Self {
        Self
    }
}

// ---------------------------------------------------------------------------------------
// SEGMENT MARKS. A region scope needs a lexical block; the node loop is one 4,600-line body
// with a dozen `continue`s, so the scopes cannot bisect it. A MARK instead attributes every
// allocation since the previous mark to a numbered segment, which bisects a straight-line
// body with no restructuring at all. Segment `i` = "allocations between mark i-1 and mark i".
// An early `continue` simply rolls its tail into the next mark that runs (slot 0, the loop
// top), which the hit counts make visible.
// ---------------------------------------------------------------------------------------

/// How many segments the node loop is cut into.
#[cfg(feature = "acensus")]
pub(crate) const N_SEGS: usize = 24;
#[cfg(feature = "acensus")]
static SEG_N: [AtomicU64; N_SEGS] = [const { AtomicU64::new(0) }; N_SEGS];
#[cfg(feature = "acensus")]
static SEG_HITS: [AtomicU64; N_SEGS] = [const { AtomicU64::new(0) }; N_SEGS];
#[cfg(feature = "acensus")]
static SEG_LAST: AtomicU64 = AtomicU64::new(0);

/// Close the running segment and open segment `slot`. Inert when disarmed.
#[cfg(feature = "acensus")]
#[inline]
pub(crate) fn mark(slot: usize) {
    if !armed() {
        return;
    }
    let now = allocs();
    let prev = SEG_LAST.swap(now, Ordering::Relaxed);
    SEG_N[slot].fetch_add(now.wrapping_sub(prev), Ordering::Relaxed);
    SEG_HITS[slot].fetch_add(1, Ordering::Relaxed);
}

/// FEATURE OFF: erased, see `Scope`.
#[cfg(not(feature = "acensus"))]
#[inline(always)]
pub(crate) const fn mark(_slot: usize) {}

/// The segment census. Empty unless the crate was built with the `acensus` feature.
#[cfg(not(feature = "acensus"))]
pub fn dump_segments(_nodes: u64) -> String {
    String::new()
}

/// The segment census.
#[cfg(feature = "acensus")]
pub fn dump_segments(nodes: u64) -> String {
    let total = allocs();
    if total == 0 {
        return String::new();
    }
    let mut s = String::new();
    for i in 0..N_SEGS {
        let h = SEG_HITS[i].load(Ordering::Relaxed);
        if h == 0 {
            continue;
        }
        let n = SEG_N[i].load(Ordering::Relaxed);
        s.push_str(&format!(
            "acensus seg{i:<3} allocs={n} hits={h} per_hit={:.3} per_node={:.3} \
             pct_of_total={:.2}%\n",
            n as f64 / h as f64,
            n as f64 / nodes.max(1) as f64,
            100.0 * n as f64 / total as f64,
        ));
    }
    s
}

/// The census, one line per region plus a process total. Empty when nothing was counted.
#[cfg(feature = "acensus")]
pub fn dump(nodes: u64) -> String {
    let total = allocs();
    if total == 0 {
        return String::new();
    }
    let mut s = format!(
        "acensus total: allocs={total} bytes={} deallocs={} nodes={nodes} \
         allocs_per_node={:.2} bytes_per_node={:.1}\n",
        alloc_bytes(),
        deallocs(),
        total as f64 / nodes.max(1) as f64,
        alloc_bytes() as f64 / nodes.max(1) as f64,
    );
    for i in 0..N_REGIONS {
        let n = REG_N[i].load(Ordering::Relaxed);
        let e = REG_ENTERS[i].load(Ordering::Relaxed);
        if e == 0 {
            continue;
        }
        s.push_str(&format!(
            "acensus {:<12} allocs={n} bytes={} enters={e} per_enter={:.3} \
             pct_of_total={:.2}%\n",
            NAMES[i],
            REG_B[i].load(Ordering::Relaxed),
            n as f64 / e as f64,
            100.0 * n as f64 / total as f64,
        ));
    }
    s
}

/// FEATURE OFF: the process total is still meaningful (the counting allocator is in the
/// binary, not behind the feature), but there are no regions to report.
#[cfg(not(feature = "acensus"))]
pub fn dump(nodes: u64) -> String {
    let total = allocs();
    if total == 0 {
        return String::new();
    }
    format!(
        "acensus total: allocs={total} bytes={} deallocs={} nodes={nodes} \
         allocs_per_node={:.2} bytes_per_node={:.1}\n",
        alloc_bytes(),
        deallocs(),
        total as f64 / nodes.max(1) as f64,
        alloc_bytes() as f64 / nodes.max(1) as f64,
    )
}
