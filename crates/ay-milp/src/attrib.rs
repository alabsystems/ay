// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ATTRIBUTION INSTRUMENTATION (measurement only; no behaviour change).
//!
//! Every counter here is a `Relaxed` atomic bumped on a path the search
//! already takes, and every dump is gated behind `the attrib knob`. Nothing in
//! this module can change a verdict, a bound, or a proof: it only counts.
//!
//! The question this exists to answer: on mas74 the process runs ~1.1M
//! `solve_bounded` calls against a MAIN tree of ~190k nodes, which reads as
//! "5.5 LP solves per node". This module attributes each solve to its exact
//! `file:line`, counts how many DISTINCT B&B trees the process runs, and
//! separates per-node work from per-subsolve setup work.

use std::sync::atomic::{AtomicU64, Ordering::Relaxed};

/// Master gate. Everything in this module is inert unless set.
pub(crate) fn on() -> bool {
    static B: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *B.get_or_init(|| crate::tune::caller_flag(crate::tune::Knob::Attrib) == Some(true))
}

// ---------------------------------------------------------------- LP sites --

/// Per-call-site `solve_bounded` census, keyed by `#[track_caller]` location.
/// `BTreeMap::new` is const, so this needs no lazy init.
pub(crate) static SOLVE_SITES: std::sync::Mutex<
    std::collections::BTreeMap<(&'static str, u32), u64>,
> = std::sync::Mutex::new(std::collections::BTreeMap::new());

#[inline]
pub(crate) fn record_solve_site(loc: &'static std::panic::Location<'static>) {
    if let Ok(mut m) = SOLVE_SITES.lock() {
        *m.entry((loc.file(), loc.line())).or_insert(0) += 1;
    }
}

// ------------------------------------------------------------- sub-solves --

/// How many DISTINCT `solve_milp_in` invocations (i.e. B&B trees) the process
/// ran, and how deep the recursion nested. The main tree is one of them.
pub(crate) static SUBSOLVE_CALLS: AtomicU64 = AtomicU64::new(0);
/// Nodes summed over EVERY tree (the process-wide node count).
pub(crate) static SUBSOLVE_NODES: AtomicU64 = AtomicU64::new(0);
/// Nesting depth histogram: index = recursion depth, capped at 7.
pub(crate) static SUBSOLVE_DEPTH: [AtomicU64; 8] = [
    AtomicU64::new(0),
    AtomicU64::new(0),
    AtomicU64::new(0),
    AtomicU64::new(0),
    AtomicU64::new(0),
    AtomicU64::new(0),
    AtomicU64::new(0),
    AtomicU64::new(0),
];
thread_local! {
    pub(crate) static SUBSOLVE_LEVEL: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}
/// Scoped depth tracker for one `solve_milp_in` invocation.
pub(crate) struct SubsolveScope(usize);
impl SubsolveScope {
    #[inline]
    pub(crate) fn new() -> Self {
        let d = SUBSOLVE_LEVEL.with(|c| {
            let d = c.get();
            c.set(d + 1);
            d
        });
        SUBSOLVE_CALLS.fetch_add(1, Relaxed);
        SUBSOLVE_DEPTH[d.min(7)].fetch_add(1, Relaxed);
        SubsolveScope(d)
    }
}
impl Drop for SubsolveScope {
    #[inline]
    fn drop(&mut self) {
        SUBSOLVE_LEVEL.with(|c| c.set(self.0));
    }
}

/// Wall spent INSIDE a nested (`depth > 0`) `solve_milp_in`, summed over every
/// sub-MIP, and the per-LAUNCH-SITE split of the same. This is the partition of
/// the MAIN tree's wall that the per-phase counters miss entirely: a sub-MIP is
/// a whole solver run — presolve, root cuts, its own tree — charged to the
/// parent's clock but reported in the child's own trace block.
pub(crate) static SUBSOLVE_NANOS: AtomicU64 = AtomicU64::new(0);
pub(crate) static SUBSOLVE_SITES: std::sync::Mutex<
    std::collections::BTreeMap<&'static str, (u64, u64)>,
> = std::sync::Mutex::new(std::collections::BTreeMap::new());

thread_local! {
    static LAUNCH: std::cell::Cell<&'static str> = const { std::cell::Cell::new("(untagged)") };
}
/// Names the sub-MIP lane the next nested `solve_milp_in` belongs to.
/// (`#[track_caller]` cannot be used here: annotating `solve_milp_in` makes
/// every nested `#[track_caller]` call inside it — including `solve_bounded` —
/// inherit the OUTER location, which destroys the LP-site census.)
pub(crate) struct LaunchTag(&'static str);
impl LaunchTag {
    #[inline]
    pub(crate) fn new(name: &'static str) -> Self {
        LaunchTag(LAUNCH.with(|c| c.replace(name)))
    }
}
impl Drop for LaunchTag {
    #[inline]
    fn drop(&mut self) {
        LAUNCH.with(|c| c.set(self.0));
    }
}
#[inline]
pub(crate) fn launch_tag() -> &'static str {
    LAUNCH.with(std::cell::Cell::get)
}

#[inline]
pub(crate) fn record_subsolve_site(name: &'static str, nanos: u64) {
    if let Ok(mut m) = SUBSOLVE_SITES.lock() {
        let e = m.entry(name).or_insert((0, 0));
        e.0 += 1;
        e.1 += nanos;
    }
}

/// `solve_bounded` wall and count split by TREE LEVEL: index 0 = the user's
/// main tree, index 1 = anything inside a nested sub-MIP. Without this split the
/// process-wide `ALLLP` total cannot be attributed to a lane.
pub(crate) static LP_NANOS_BY_LEVEL: [AtomicU64; 2] = [AtomicU64::new(0), AtomicU64::new(0)];
pub(crate) static LP_CALLS_BY_LEVEL: [AtomicU64; 2] = [AtomicU64::new(0), AtomicU64::new(0)];
/// Wall inside the node-loop BODY (one accumulation per iteration, `continue`
/// paths included), split by tree level. Everything a node costs — LP, bound,
/// branching, heuristics it fires, sub-MIPs it launches — is inside this.
pub(crate) static NODE_BODY_NANOS: [AtomicU64; 2] = [AtomicU64::new(0), AtomicU64::new(0)];
pub(crate) static NODE_BODY_ITERS: [AtomicU64; 2] = [AtomicU64::new(0), AtomicU64::new(0)];

#[inline]
pub(crate) fn level() -> usize {
    usize::from(SUBSOLVE_LEVEL.with(std::cell::Cell::get) > 1)
}

/// Setup wall spent BEFORE a tree's node loop starts (presolve + root cuts +
/// model build), summed over every invocation, split by nesting depth 0 (the
/// main tree) vs >0 (sub-MIPs). Wall, so LOAD-SENSITIVE — read the CALLS and
/// ROUNDS counters as the load-invariant evidence.
pub(crate) static SETUP_NANOS_ROOT: AtomicU64 = AtomicU64::new(0);
pub(crate) static SETUP_NANOS_SUB: AtomicU64 = AtomicU64::new(0);
pub(crate) static ROOTCUT_NANOS_ROOT: AtomicU64 = AtomicU64::new(0);
pub(crate) static ROOTCUT_NANOS_SUB: AtomicU64 = AtomicU64::new(0);
/// A SECOND root-cut lane, invisible to every existing phase counter: the
/// primal-restart path re-runs `add_root_cuts_rounds` on the heuristic model
/// from INSIDE the node loop (bab.rs, "restart separation").
pub(crate) static ROOTCUT_RESTART_CALLS: AtomicU64 = AtomicU64::new(0);
pub(crate) static ROOTCUT_RESTART_NANOS: AtomicU64 = AtomicU64::new(0);

// ------------------------------------------------------- cut separation ----

/// Cut-family separation census. Index into `SEP_LABELS`.
pub(crate) const SEP_N: usize = 16;
pub(crate) const SEP_LABELS: [&str; SEP_N] = [
    "covers",
    "mir",
    "strongcg",
    "mixing",
    "lifted_cover",
    "implied_bound",
    "lift_project",
    "flow_cover",
    "clique",
    "odd_cycle",
    "flow_cover_agg",
    "gmi_exact",
    "mir_tableau",
    "zero_half",
    "mir_agg",
    "node-sep",
];
macro_rules! zeros {
    ($n:expr) => {
        [const { AtomicU64::new(0) }; $n]
    };
}
/// Calls into each family's separator.
pub(crate) static SEP_CALLS: [AtomicU64; SEP_N] = zeros!(SEP_N);
/// Cuts the family DERIVED (returned, before any filtering).
pub(crate) static SEP_DERIVED: [AtomicU64; SEP_N] = zeros!(SEP_N);
/// Wall inside the family (load-sensitive; secondary evidence).
pub(crate) static SEP_NANOS: [AtomicU64; SEP_N] = zeros!(SEP_N);

/// Cuts that reached the round's admission filter, and the ones that survived
/// it to become real rows. `DERIVED - ADMITTED` is the round's pure waste.
pub(crate) static CUT_ROUNDS: AtomicU64 = AtomicU64::new(0);
pub(crate) static CUT_OFFERED: AtomicU64 = AtomicU64::new(0);
pub(crate) static CUT_ADMITTED: AtomicU64 = AtomicU64::new(0);

/// The two exact-rational rounding kernels the macOS `sample` profile named.
pub(crate) static MIR_ROUND_CALLS: AtomicU64 = AtomicU64::new(0);
pub(crate) static MIR_ROUND_SOME: AtomicU64 = AtomicU64::new(0);
pub(crate) static STRONGCG_ROUND_CALLS: AtomicU64 = AtomicU64::new(0);
pub(crate) static STRONGCG_ROUND_SOME: AtomicU64 = AtomicU64::new(0);

#[inline]
pub(crate) fn sep_record(idx: usize, produced: usize, nanos: u64) {
    SEP_CALLS[idx].fetch_add(1, Relaxed);
    SEP_DERIVED[idx].fetch_add(produced as u64, Relaxed);
    SEP_NANOS[idx].fetch_add(nanos, Relaxed);
}

// ------------------------------------------------ per-node object churn ----

pub(crate) static FEASCHECK_NEW: AtomicU64 = AtomicU64::new(0);
pub(crate) static FEASCHECK_NANOS: AtomicU64 = AtomicU64::new(0);
pub(crate) static FEASCHECK_NNZ: AtomicU64 = AtomicU64::new(0);
pub(crate) static SAFE_BOUND_CALLS: AtomicU64 = AtomicU64::new(0);
pub(crate) static SAFE_BOUND_NANOS: AtomicU64 = AtomicU64::new(0);

// ------------------------------------------------------------ allocation ---

/// Fed by the counting global allocator installed in `examples/mps_solve.rs`.
/// `pub` so the example (a separate crate-level target) can reach them.
pub static ALLOC_COUNT: AtomicU64 = AtomicU64::new(0);
pub static ALLOC_BYTES: AtomicU64 = AtomicU64::new(0);
pub static REALLOC_COUNT: AtomicU64 = AtomicU64::new(0);
pub static DEALLOC_COUNT: AtomicU64 = AtomicU64::new(0);

/// Allocation counts captured at region boundaries, so a region's share is a
/// difference of two snapshots. Index into `ALLOC_REGION_LABELS`.
pub(crate) const AREG_N: usize = 8;
pub(crate) const ALLOC_REGION_LABELS: [&str; AREG_N] = [
    "presolve+prep",
    "root-cut-loop",
    "node-lp(primary)",
    "node-bound(safe_bound)",
    "restart-root-cuts",
    "node-bound(exact/rational)",
    "node-branch+push_children",
    "primal-heur(pump/climb/swap)",
];
pub(crate) static AREG_COUNT: [AtomicU64; AREG_N] = zeros!(AREG_N);
pub(crate) static AREG_BYTES: [AtomicU64; AREG_N] = zeros!(AREG_N);
pub(crate) static AREG_ENTERS: [AtomicU64; AREG_N] = zeros!(AREG_N);

/// Charge one region with the allocations made inside it. Cheap: two relaxed
/// loads on entry, two on exit. Nesting is NOT handled (an inner region's
/// allocations are charged to both), which is why the labels are disjoint
/// spans of the node body.
pub(crate) struct AllocRegion(usize, u64, u64);
impl AllocRegion {
    #[inline]
    pub(crate) fn new(idx: usize) -> Option<Self> {
        on().then(|| {
            AREG_ENTERS[idx].fetch_add(1, Relaxed);
            AllocRegion(idx, ALLOC_COUNT.load(Relaxed), ALLOC_BYTES.load(Relaxed))
        })
    }
}
impl Drop for AllocRegion {
    #[inline]
    fn drop(&mut self) {
        AREG_COUNT[self.0].fetch_add(ALLOC_COUNT.load(Relaxed).wrapping_sub(self.1), Relaxed);
        AREG_BYTES[self.0].fetch_add(ALLOC_BYTES.load(Relaxed).wrapping_sub(self.2), Relaxed);
    }
}

// ----------------------------------------------------------------- dump ----

/// Print the whole census. Called once at the end of the OUTERMOST
/// `solve_milp_in` (depth 0).
pub(crate) fn dump() {
    if !on() {
        return;
    }
    let calls = SUBSOLVE_CALLS.load(Relaxed);
    let nodes = SUBSOLVE_NODES.load(Relaxed);
    dump_solve_totals(calls, nodes);
    dump_lp_sites(nodes);
    dump_separator_stats(nodes);
    dump_allocation_stats(nodes);
}

fn dump_solve_totals(calls: u64, nodes: u64) {
    eprintln!(
        "attrib SUBSOLVES calls={calls} nodes_all_trees={nodes} depth_hist={:?}",
        SUBSOLVE_DEPTH
            .iter()
            .map(|c| c.load(Relaxed))
            .collect::<Vec<_>>()
    );
    eprintln!(
        "attrib NODEBODY main-tree={:.2}s over {} iters | in-sub-MIP={:.2}s over {} iters",
        NODE_BODY_NANOS[0].load(Relaxed) as f64 / 1e9,
        NODE_BODY_ITERS[0].load(Relaxed),
        NODE_BODY_NANOS[1].load(Relaxed) as f64 / 1e9,
        NODE_BODY_ITERS[1].load(Relaxed),
    );
    eprintln!(
        "attrib LPWALL main-tree={:.2}s ({} calls) | in-sub-MIP={:.2}s ({} calls)",
        LP_NANOS_BY_LEVEL[0].load(Relaxed) as f64 / 1e9,
        LP_CALLS_BY_LEVEL[0].load(Relaxed),
        LP_NANOS_BY_LEVEL[1].load(Relaxed) as f64 / 1e9,
        LP_CALLS_BY_LEVEL[1].load(Relaxed),
    );
    eprintln!(
        "attrib SUBSOLVE-WALL total_in_nested={:.2}s",
        SUBSOLVE_NANOS.load(Relaxed) as f64 / 1e9
    );
    if let Ok(m) = SUBSOLVE_SITES.lock() {
        let mut v: Vec<_> = m.iter().map(|(&k, &e)| (e, k)).collect();
        v.sort_unstable_by(|a, b| b.0 .1.cmp(&a.0 .1));
        for ((n, ns), name) in v {
            eprintln!(
                "attrib   launch {name}: calls={n} wall={:.2}s ({:.2}s/call)",
                ns as f64 / 1e9,
                ns as f64 / 1e9 / n.max(1) as f64
            );
        }
    }
    eprintln!(
        "attrib SETUP root={:.2}s (rootcuts {:.2}s) | sub={:.2}s (rootcuts {:.2}s) \
         | restart-rootcuts {}x {:.2}s",
        SETUP_NANOS_ROOT.load(Relaxed) as f64 / 1e9,
        ROOTCUT_NANOS_ROOT.load(Relaxed) as f64 / 1e9,
        SETUP_NANOS_SUB.load(Relaxed) as f64 / 1e9,
        ROOTCUT_NANOS_SUB.load(Relaxed) as f64 / 1e9,
        ROOTCUT_RESTART_CALLS.load(Relaxed),
        ROOTCUT_RESTART_NANOS.load(Relaxed) as f64 / 1e9,
    );
}

fn dump_lp_sites(nodes: u64) {
    if let Ok(m) = SOLVE_SITES.lock() {
        let mut v: Vec<_> = m.iter().map(|(&(f, l), &c)| (c, f, l)).collect();
        v.sort_unstable_by(|a, b| b.0.cmp(&a.0));
        let tot: u64 = v.iter().map(|e| e.0).sum();
        eprintln!("attrib LPSITES total={tot} distinct={}", v.len());
        for (c, f, l) in v.iter().take(24) {
            let file = f.rsplit('/').next().unwrap_or(f);
            eprintln!(
                "attrib   {file}:{l} {c} ({:.1}%, {:.3}/node)",
                100.0 * *c as f64 / tot.max(1) as f64,
                *c as f64 / nodes.max(1) as f64,
            );
        }
    }
}

fn dump_separator_stats(nodes: u64) {
    let mut v: Vec<_> = (0..SEP_N)
        .map(|i| {
            (
                SEP_NANOS[i].load(Relaxed),
                SEP_CALLS[i].load(Relaxed),
                SEP_DERIVED[i].load(Relaxed),
                SEP_LABELS[i],
            )
        })
        .filter(|e| e.1 > 0)
        .collect();
    v.sort_unstable_by(|a, b| b.0.cmp(&a.0));
    eprintln!(
        "attrib CUTROUNDS rounds={} offered={} admitted={} (waste={})",
        CUT_ROUNDS.load(Relaxed),
        CUT_OFFERED.load(Relaxed),
        CUT_ADMITTED.load(Relaxed),
        CUT_OFFERED
            .load(Relaxed)
            .saturating_sub(CUT_ADMITTED.load(Relaxed)),
    );
    for (ns, c, d, lbl) in v {
        eprintln!(
            "attrib   sep {lbl}: calls={c} derived={d} time={:.2}s",
            ns as f64 / 1e9
        );
    }
    eprintln!(
        "attrib ROUNDKERNEL mir_round={}({} some) strongcg_round={}({} some)",
        MIR_ROUND_CALLS.load(Relaxed),
        MIR_ROUND_SOME.load(Relaxed),
        STRONGCG_ROUND_CALLS.load(Relaxed),
        STRONGCG_ROUND_SOME.load(Relaxed),
    );
    eprintln!(
        "attrib FEASCHECK new={} nnz={} time={:.2}s | SAFEBOUND calls={} ({:.3}/node) time={:.2}s",
        FEASCHECK_NEW.load(Relaxed),
        FEASCHECK_NNZ.load(Relaxed),
        FEASCHECK_NANOS.load(Relaxed) as f64 / 1e9,
        SAFE_BOUND_CALLS.load(Relaxed),
        SAFE_BOUND_CALLS.load(Relaxed) as f64 / nodes.max(1) as f64,
        SAFE_BOUND_NANOS.load(Relaxed) as f64 / 1e9,
    );
}

fn dump_allocation_stats(nodes: u64) {
    let ac = ALLOC_COUNT.load(Relaxed);
    let ab = ALLOC_BYTES.load(Relaxed);
    if ac > 0 {
        eprintln!(
            "attrib ALLOC total={ac} ({:.1}/node) bytes={ab} ({:.0} B/node) realloc={} dealloc={}",
            ac as f64 / nodes.max(1) as f64,
            ab as f64 / nodes.max(1) as f64,
            REALLOC_COUNT.load(Relaxed),
            DEALLOC_COUNT.load(Relaxed),
        );
        for i in 0..AREG_N {
            let c = AREG_COUNT[i].load(Relaxed);
            if c == 0 {
                continue;
            }
            eprintln!(
                "attrib   alloc {}: enters={} count={c} ({:.1}%) bytes={} ({:.1}/enter)",
                ALLOC_REGION_LABELS[i],
                AREG_ENTERS[i].load(Relaxed),
                100.0 * c as f64 / ac.max(1) as f64,
                AREG_BYTES[i].load(Relaxed),
                c as f64 / AREG_ENTERS[i].load(Relaxed).max(1) as f64,
            );
        }
    }
}
