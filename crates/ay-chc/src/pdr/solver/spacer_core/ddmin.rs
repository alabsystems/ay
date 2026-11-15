// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QuickXplain over a monotone predicate (`DESIGN` §4.2.4). Owner: **WP-B1-L**.
//!
//! Invariant (lock L-Q): `Unknown` is "not UNSAT"; every returned set is
//! grounded in an OBSERVED UNSAT; on budget exhaustion the best grounded set
//! is returned (initially the input mask, justified by the caller).
//! ≈ `2k·log2(n/k) + 2k` tests for core size `k`; for `n ≤ min_lits` a linear loop.

#![allow(dead_code, unused)]

use super::oracle::{Budget, Hyp, Verdict};
use crate::pdr::cube::literals::LitCube;
use crate::pdr::solver::PdrSolver;
use crate::PredicateId;

/// Junker's recursion over `is_unsat(mask, budget) -> Some(true) | Some(false) | None (Unknown)`.
///
/// `mask` is the starting set (must be observed-UNSAT by the caller); returns
/// `(core_mask, exact)` where `exact` is true iff the recursion completed
/// within `budget` (every literal of the result was tested necessary, modulo
/// `Unknown` answers, which keep a literal).
///
/// Grounding argument (L-Q). `QX(B, δ, C)` has the precondition "`B ∪ C` is
/// UNSAT" and the postcondition "`B ∪ Δ` is UNSAT" for the returned `Δ ⊆ C`:
/// the shortcut returns `∅` only after an OBSERVED UNSAT of `B`; the base
/// case returns `C` itself (precondition); the two recursive calls chain
/// postcondition into precondition. `Unknown` only skips the shortcut, so it
/// never breaks the chain — it costs minimality, never soundness. On budget
/// exhaustion every frame returns its own `C`, which the same chain keeps
/// UNSAT together with its base, so the returned set is still grounded.
pub(in crate::pdr::solver) fn quickxplain<F>(
    mask: &[bool],
    min_lits: usize,
    budget: &mut Budget,
    mut is_unsat: F,
) -> (Vec<bool>, bool)
where
    F: FnMut(&[bool], &mut Budget) -> Option<bool>,
{
    let n = mask.len();
    let members: Vec<usize> = (0..n).filter(|&i| mask[i]).collect();
    if members.len() <= 1 {
        return (mask.to_vec(), true);
    }
    if members.len() <= min_lits {
        // Linear deletion loop: try to drop each member in turn; every
        // adopted `keep` was observed UNSAT.
        let mut keep = mask.to_vec();
        let mut exhausted = false;
        for &i in &members {
            if budget.exhausted() {
                exhausted = true;
                break;
            }
            keep[i] = false;
            if is_unsat(&keep, budget) != Some(true) {
                keep[i] = true;
            }
        }
        return (keep, !exhausted);
    }
    let mut st = QxState {
        exhausted: false,
        n,
    };
    let core = qx_rec(&[], false, &members, &mut st, budget, &mut is_unsat);
    let mut out = vec![false; n];
    for i in core {
        out[i] = true;
    }
    (out, !st.exhausted)
}

struct QxState {
    exhausted: bool,
    n: usize,
}

/// `qx_rec(B, has_delta, C)`: some `C' ⊆ C` with `B ∪ C'` UNSAT (minimal when
/// the oracle answers exactly), assuming `B ∪ C` is UNSAT. `has_delta` says
/// whether `B` grew since the last check (Junker's δ ≠ ∅ shortcut).
fn qx_rec<F>(
    base: &[usize],
    has_delta: bool,
    cands: &[usize],
    st: &mut QxState,
    budget: &mut Budget,
    is_unsat: &mut F,
) -> Vec<usize>
where
    F: FnMut(&[bool], &mut Budget) -> Option<bool>,
{
    if st.exhausted {
        return cands.to_vec();
    }
    if has_delta {
        if budget.exhausted() {
            st.exhausted = true;
            return cands.to_vec();
        }
        let m = to_mask(st.n, base, &[]);
        if is_unsat(&m, budget) == Some(true) {
            return Vec::new();
        }
    }
    if cands.len() == 1 {
        return cands.to_vec();
    }
    let k = cands.len() / 2;
    let (c1, c2) = cands.split_at(k);
    // Δ2 ⊆ C2 with B ∪ C1 ∪ Δ2 UNSAT.
    let mut b1: Vec<usize> = base.to_vec();
    b1.extend_from_slice(c1);
    let d2 = qx_rec(&b1, !c1.is_empty(), c2, st, budget, is_unsat);
    if st.exhausted {
        let mut out = c1.to_vec();
        out.extend(d2);
        return out;
    }
    // Δ1 ⊆ C1 with B ∪ Δ2 ∪ Δ1 UNSAT.
    let mut b2: Vec<usize> = base.to_vec();
    b2.extend_from_slice(&d2);
    let d1 = qx_rec(&b2, !d2.is_empty(), c1, st, budget, is_unsat);
    let mut out = d1;
    out.extend(d2);
    out
}

fn to_mask(n: usize, a: &[usize], b: &[usize]) -> Vec<bool> {
    let mut m = vec![false; n];
    for &i in a.iter().chain(b.iter()) {
        m[i] = true;
    }
    m
}

impl PdrSolver {
    /// QuickXplain with `P(S) := oracle_check_all_clauses(pred, level, full.subset(S), Reach)` UNSAT.
    pub(in crate::pdr::solver) fn quickxplain_reach(
        &mut self,
        pred: PredicateId,
        level: usize,
        full: &LitCube,
        mask: &[bool],
        budget: &mut Budget,
    ) -> (Vec<bool>, bool) {
        let min_lits = self.config.spacer.ddmin_min_lits;
        quickxplain(mask, min_lits, budget, |m, budget| {
            if self.is_cancelled() {
                return None;
            }
            self.spacer_stats.ind_gen_queries_a += 1;
            let sub = full.subset(m);
            match self
                .oracle_check_all_clauses_opts(pred, level, &sub, Hyp::Reach, false, budget)
                .0
            {
                Verdict::Unsat { .. } => Some(true),
                Verdict::Sat(_) => Some(false),
                Verdict::Unknown => None,
            }
        })
    }
}
