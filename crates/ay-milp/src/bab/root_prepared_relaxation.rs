// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact root-relaxation handoff into the first branch-and-bound node.

use std::sync::Arc;

use num_rational::BigRational;

use super::{Candidate, FloatLp, Node, SimplexStatus};

/// One prefix relaxation prepared by an owned worker LP.
///
/// The box is retained verbatim because root reduced-cost fixing and
/// propagation may tighten it before the node is consumed. A result is advice
/// only unless that box still matches exactly and the LP's fixed-slot rows have
/// not been rewritten; either mismatch discards it and the serial engine solves
/// the current relaxation normally.
pub(super) struct PreparedNodeRelaxation {
    pub(super) lower: Vec<f64>,
    pub(super) upper: Vec<f64>,
    pub(super) candidate: Candidate,
}

/// Reuse the root solve as the root node's relaxation only when it is exactly
/// the answer that the node would compute again.
///
/// The root heuristics may tighten `lower`/`upper` after the root LP has been
/// solved.  In that case this deliberately declines and the ordinary node path
/// re-solves the narrower box.  The shape checks keep the direct prepared lane
/// fail-closed even if a future simplex result is partial.
///
/// `the no-root-warm knob` declines unconditionally, restoring the historical
/// COLD re-solve so the duplicate solve can be A/B'd rather than only
/// node-capped (see [`super::no_root_warm`]).
pub(super) fn prepare_root_relaxation(
    lp: &FloatLp,
    root: &Candidate,
    lower: &[f64],
    upper: &[f64],
) -> Option<PreparedNodeRelaxation> {
    (root.status == SimplexStatus::Optimal
        && root.basis.len() == lp.m
        && root.at.len() == lp.cols
        && root.values.len() == lp.cols
        && root.duals.len() == lp.m
        && !lp.cut_slots_live.get()
        && !super::no_root_warm()
        && lower == lp.lower
        && upper == lp.upper)
        .then(|| PreparedNodeRelaxation {
            lower: lower.to_vec(),
            upper: upper.to_vec(),
            candidate: root.clone(),
        })
}

/// Final row-identity check at the prepared Candidate's consumption boundary.
/// A cut-slot reload preserves both dimensions and bounds, so it is invisible
/// to the ordinary stale-box checks; `cut_slots_live` is the matrix-generation
/// latch for exactly that case.
pub(super) fn revalidate_prepared_relaxation(
    lp: &FloatLp,
    prepared: Option<PreparedNodeRelaxation>,
    stale: &mut usize,
) -> Option<PreparedNodeRelaxation> {
    if prepared.is_some() && lp.cut_slots_live.get() {
        *stale += 1;
        None
    } else {
        prepared
    }
}

/// Build the ordinary root node around already-authorized prepared advice.
///
/// The caller computes the advice immediately before this call, after all root
/// tightening. Node propagation and local cuts revalidate it again at the
/// consumption boundary.
pub(super) fn root_node(
    cover: Option<Arc<BigRational>>,
    prepared: Option<PreparedNodeRelaxation>,
    cap: u32,
) -> Node {
    Node {
        depth: 0,
        fixes: None,
        sym_seq: None,
        bound: None,
        bkey: f64::NAN,
        cover,
        warm: None,
        from_branch: None,
        structural_seeds: None,
        raw_bound: None,
        cap,
        prepared,
    }
}

#[cfg(test)]
thread_local! {
    /// Test-only observation of the actual direct-consumption path. Thread
    /// local keeps parallel tests from contaminating the node-cap guard.
    pub(super) static ROOT_PREPARED_CONSUMED: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}
