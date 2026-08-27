// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! FORGONE COST: what a size gate's cheap branch actually costs.
//!
//! # The defect this measures
//!
//! the development design notes names the shape. A
//! pass has an expensive-but-better variant, someone measures the variant losing on
//! small inputs, and adds `if size >= MIN`. But size proxies only the cheap path's
//! **per-invocation** cost, and the total is per-invocation × **invocation count**.
//! A small problem that invokes the cheap path tens of thousands of times gets the
//! worst of both and is invisible to the gate, because it looks small.
//!
//! Found four times in EUF. One instance was costing a **correct answer**, not time:
//! `QF_AX/swap/swap_invalid_t1_np_sf_ai_00010_009.cvc` is `sat`, z3 agrees, and the
//! rebuild path abandoned it as `unknown` in 4.2 s while the incremental path
//! answered in 2.0 s.
//!
//! # Why fire rate cannot find it
//!
//! `1c1ce672c` measured four separator families at fire rate **zero** and reached
//! four *different* verdicts — two correctly silent, one wrongly gated and worth a
//! verdict, one net-negative to broaden. What separates them is the **sign of the
//! delta**, which a count of firings does not carry. So this census records the
//! *cost the gate asserts is negligible*, on the branch the gate forces, in the
//! gate's own units.
//!
//! # Why the doc comment is the specification
//!
//! Every gate here documents a quantitative claim. `CONG_UNDO_MIN_FUNC_APPS` says
//! the cheap path wins on *"merge-heavy / pop-light solves whose func_apps set is
//! small enough that the rebuild was already cheap"*. Both factors are at the call
//! site. Charging the claim is therefore free, needs no benchmark chosen in advance,
//! and needs no candidate feature nominated with hindsight — which is what makes it
//! usable on gates nobody has audited. `SIZE_GATE_ANTIPATTERN.md` left five gates
//! unaudited *"because this session has no benchmark that exercises them"*; a
//! forgone-cost counter needs no such benchmark, and that is the point.
//!
//! # Cost
//!
//! One relaxed `fetch_add` per not-taken evaluation, counts only, no wall clock. The
//! line reproduces on a contended box. Always on: a number that appears only when
//! somebody already suspects a problem cannot report a problem nobody suspects, and
//! every instance of this defect class so far was found by suspicion.

use std::sync::atomic::{AtomicU64, Ordering};

/// A gate whose cheap branch is being charged.
///
/// One entry per audited gate. The `&'static str` is the gate's constant name, so a
/// report names the thing to go and read.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Site {
    /// The gate constant, e.g. `"PHASE_EPOCH_MIN_ATOMS"`.
    pub gate: &'static str,
    /// The unit the cost is counted in, e.g. `"atoms scanned"`.
    pub unit: &'static str,
}

/// The audited gates, in declaration order. Index into `COSTS` / `HITS`.
///
/// These are exactly the five `SIZE_GATE_ANTIPATTERN.md` lists as unaudited, plus
/// their duplicate. Adding a gate here is how it gets audited; the constant's own
/// doc comment says what to charge.
pub const SITES: &[Site] = &[
    Site {
        gate: "PHASE_EPOCH_MIN_ATOMS (ay-dpll combiner)",
        unit: "LRA atoms below the floor",
    },
    Site {
        gate: "PHASE_EPOCH_MIN_ATOMS (ay-lia theory_impl)",
        unit: "atoms below the floor",
    },
    Site {
        gate: "COUNTING_MIN_TERMS (ay-pb propagation)",
        unit: "constraint terms below the floor",
    },
    Site {
        gate: "ONE_ROW_NEGATIVE_KNAP_MIN_TERMS (ay-pb portfolio)",
        unit: "terms below the floor",
    },
    Site {
        gate: "PERSISTENT_BOUND_MIN_TERMS (ay-pb optimize)",
        unit: "weighted literals below the floor",
    },
    Site {
        gate: "DEFAULT_CONDENSE_MEAN_NODE_GATE (ay-chc)",
        // INVERTED: this gate refuses ABOVE a ceiling, so it forgoes condensing the
        // largest problems rather than the smallest.
        unit: "mean constraint nodes above the ceiling",
    },
];

/// Index of the ay-dpll combiner's phase-epoch gate.
pub const PHASE_EPOCH_COMBINER: usize = 0;
/// Index of the ay-lia phase-epoch gate — the SAME constant, declared twice with no
/// shared definition (`SIZE_GATE_ANTIPATTERN.md` flags the duplication).
pub const PHASE_EPOCH_LIA: usize = 1;
/// Index of ay-pb's counting-propagation gate.
pub const PB_COUNTING: usize = 2;
/// Index of ay-pb's one-row negative-knapsack gate.
pub const PB_ONE_ROW_KNAP: usize = 3;
/// Index of ay-pb's persistent-bound gate.
pub const PB_PERSISTENT_BOUND: usize = 4;
/// Index of ay-chc's condense gate.
pub const CHC_CONDENSE: usize = 5;

const N: usize = 6;

/// Summed cost charged to the cheap branch, per site.
static COSTS: [AtomicU64; N] = [const { AtomicU64::new(0) }; N];
/// Times the gate sent work down the cheap branch, per site.
static HITS: [AtomicU64; N] = [const { AtomicU64::new(0) }; N];

/// Charge `cost` to `site`'s cheap branch. Call on the NOT-TAKEN side of the gate.
///
/// `cost` is in the gate's own units — whatever quantity its doc comment claims is
/// small. Saturating, because a counter that wraps is worse than one that pins.
#[inline]
pub fn charge(site: usize, cost: u64) {
    if let (Some(c), Some(h)) = (COSTS.get(site), HITS.get(site)) {
        c.fetch_add(cost, Ordering::Relaxed);
        h.fetch_add(1, Ordering::Relaxed);
    }
}

/// `(hits, summed cost)` for `site`.
#[must_use]
pub fn read(site: usize) -> (u64, u64) {
    match (HITS.get(site), COSTS.get(site)) {
        (Some(h), Some(c)) => (h.load(Ordering::Relaxed), c.load(Ordering::Relaxed)),
        _ => (0, 0),
    }
}

/// Every site with a non-zero charge, as `(site, hits, cost)`.
///
/// A site with many hits and a large cost is a gate forcing a lot of work down the
/// branch it calls cheap — the signature of the antipattern. A site that never fires
/// is not evidence of anything and is omitted rather than reported as clean.
#[must_use]
pub fn report() -> Vec<(&'static Site, u64, u64)> {
    SITES
        .iter()
        .enumerate()
        .filter_map(|(i, s)| {
            let (hits, cost) = read(i);
            (hits > 0).then_some((s, hits, cost))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_site_has_an_index_and_a_unit() {
        assert_eq!(SITES.len(), N, "SITES and the counter arrays must agree");
        for s in SITES {
            assert!(!s.gate.is_empty() && !s.unit.is_empty());
        }
        // The index constants must address distinct, in-range sites.
        let idx = [
            PHASE_EPOCH_COMBINER,
            PHASE_EPOCH_LIA,
            PB_COUNTING,
            PB_ONE_ROW_KNAP,
            PB_PERSISTENT_BOUND,
            CHC_CONDENSE,
        ];
        let mut seen = idx;
        seen.sort_unstable();
        assert_eq!(seen, [0, 1, 2, 3, 4, 5], "site indices must be distinct");
    }

    /// Hits and cost are separate because they answer different questions: hits is a
    /// fire rate and reports nothing alone, cost is what the cheap branch actually
    /// paid. `1c1ce672c` is the measured reason.
    #[test]
    fn hits_and_cost_are_recorded_apart() {
        let (h0, c0) = read(CHC_CONDENSE);
        charge(CHC_CONDENSE, 7);
        charge(CHC_CONDENSE, 5);
        let (h1, c1) = read(CHC_CONDENSE);
        assert_eq!((h1 - h0, c1 - c0), (2, 12));
    }

    /// An out-of-range site must be inert, never a panic: this is instrumentation
    /// and it runs on the default path of a solver.
    #[test]
    fn an_unknown_site_is_inert() {
        charge(usize::MAX, 1);
        assert_eq!(read(usize::MAX), (0, 0));
    }
}
