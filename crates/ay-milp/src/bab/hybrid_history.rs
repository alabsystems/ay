// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::cmp::Ordering;

use super::PropDeps;

/// HYBRID BRANCHING HISTORY (`the hybrid knob`) — the non-pseudocost half of a
/// classical hybrid branching rule.
///
/// # What this records, and why the two signals it does not record are absent
///
/// SCIP's `relpscost` blends four per-column histories: pseudocost, INFERENCE
/// (domain reductions the branch caused), CUTOFF (how often the branch's child
/// was fathomed), and CONFLICT (appearances in derived no-goods). This struct
/// carries the two that AY can attribute WITHOUT new plumbing:
///
/// * INFERENCE — [`super::propagate_branch_rows_t`] already cascades from the branched
///   column at node entry and already has a per-tightening tap ([`PropDeps`]),
///   so counting the cascade's bound changes and charging them to the column
///   that triggered it is exact and costs one `usize` increment per tightening.
///   It is LIVE ONLY where node propagation runs (`prop_on`, i.e. the mixed-model
///   gate, armed at `prop_arm`); elsewhere `infer_cnt` stays 0 and the blend
///   falls back to the cutoff term alone (see `bonus`, which normalises over the
///   signals that HAVE data rather than scoring a missing signal as zero).
/// * CUTOFF — every node knows the `(column, side)` branch that made it
///   (`Node::from_branch`), so "was this child fathomed, or did it branch again?"
///   is `visits − branched`, two counters at two sites. This one is universal:
///   it needs no lever to be on, and it accumulates on exactly the paths where
///   pseudocost learns NOTHING (a child killed by node propagation, by a stale
///   box, or by its parent's inherited bound never reaches `pc.record`).
///
/// CONFLICT is NOT recorded. AY does derive no-goods (`ng_admit`), but they are
/// admitted from a separate learning replay whose literals are the deviations of
/// the conflicting BOX, not the branch decisions on the path — charging them to
/// a branching column would need a path/decision trail the search does not keep.
/// A structural stand-in (implication-table degree, say) would be a static
/// property dressed as history, so it is left out rather than reported as a
/// conflict score.
///
/// # Attribution is per (column, SIDE)
///
/// The score is a PRODUCT of a down term and an up term, and the two sides fail
/// for different reasons — a set-partition column's `x_j >= 1` child propagates
/// a whole row to zero while its `x_j <= 0` child does nothing. Storing one
/// scalar per column would average that asymmetry away, so every counter is
/// indexed `2*j + up`.
pub(super) struct HybridHist {
    /// Children of a branch on (col, side) that were popped and materialised.
    pub(super) visits: Vec<u32>,
    /// ...and that went on to branch again (so `visits − branched` = fathoms).
    branched: Vec<u32>,
    /// Domain reductions the node-entry cascade from (col, side) produced.
    infer_sum: Vec<f64>,
    /// Cascades attributed to (col, side) — the denominator for `infer_sum`.
    pub(super) infer_cnt: Vec<u32>,
    pub(super) tot_visits: u64,
    pub(super) tot_branched: u64,
    tot_infer_sum: f64,
    pub(super) tot_infer_cnt: u64,
}

/// The tightening tap that feeds [`HybridHist::infer`]. Same monomorphisation
/// slot as [`super::NoDeps`]; the propagation's arithmetic and control flow are
/// unchanged, this only counts what it already did.
pub(super) struct CountDeps {
    pub(super) n: usize,
}
impl PropDeps for CountDeps {
    fn tighten(&mut self, _c: usize) {
        self.n += 1;
    }
}

impl HybridHist {
    pub(super) fn new(n: usize) -> Self {
        Self {
            visits: vec![0; 2 * n],
            branched: vec![0; 2 * n],
            infer_sum: vec![0.0; 2 * n],
            infer_cnt: vec![0; 2 * n],
            tot_visits: 0,
            tot_branched: 0,
            tot_infer_sum: 0.0,
            tot_infer_cnt: 0,
        }
    }

    fn slot(j: usize, up: bool) -> usize {
        2 * j + usize::from(up)
    }

    /// A child produced by branching on (`j`, `up`) has been popped.
    pub(super) fn visit(&mut self, j: usize, up: bool) {
        let k = Self::slot(j, up);
        if k < self.visits.len() {
            self.visits[k] += 1;
            self.tot_visits += 1;
        }
    }

    /// ...and it branched rather than being fathomed.
    pub(super) fn branched(&mut self, j: usize, up: bool) {
        let k = Self::slot(j, up);
        if k < self.branched.len() {
            self.branched[k] += 1;
            self.tot_branched += 1;
        }
    }

    /// The node-entry cascade from (`j`, `up`) deduced `n` bound changes.
    pub(super) fn infer(&mut self, j: usize, up: bool, n: usize) {
        let k = Self::slot(j, up);
        if k < self.infer_cnt.len() {
            self.infer_sum[k] += n as f64;
            self.infer_cnt[k] += 1;
            self.tot_infer_sum += n as f64;
            self.tot_infer_cnt += 1;
        }
    }

    /// The two global means the per-column rates are normalised against
    /// (`(inference, cutoff)`), hoisted out of the per-candidate loop exactly
    /// like [`PseudoCost::avgs`].
    pub(super) fn avgs(&self) -> (f64, f64) {
        let inf = if self.tot_infer_cnt > 0 {
            self.tot_infer_sum / self.tot_infer_cnt as f64
        } else {
            0.0
        };
        let cut = if self.tot_visits > 0 {
            (self.tot_visits - self.tot_branched.min(self.tot_visits)) as f64
                / self.tot_visits as f64
        } else {
            0.0
        };
        (inf, cut)
    }
}

/// A scoring pass's read-only view of the hybrid history: the counters plus the
/// weights and the two global means, built once per pass.
pub(super) struct HybridView<'a> {
    pub(super) h: &'a HybridHist,
    /// The reliability threshold in force (`strong_branch_effort`'s `rel`), as
    /// the denominator of the pseudocost-dominance ramp.
    pub(super) rel: f64,
    /// Overall strength of the hybrid term (`the hybrid knob_W`).
    pub(super) w: f64,
    /// Relative weights of the two signals (`the hybrid knob_INF` / `_CUT`).
    pub(super) w_inf: f64,
    pub(super) w_cut: f64,
    pub(super) inf_avg: f64,
    pub(super) cut_avg: f64,
}

impl HybridView<'_> {
    /// SCIP's component map: a rate `x` against its population mean lands in
    /// `[0, 1)` as `(x/avg) / (1 + x/avg)`, so an average column scores 0.5 and
    /// no single outlier can dominate the sum.
    fn norm(x: f64, avg: f64) -> f64 {
        // An unordered input has no usable positive signal. Spell the partial
        // order explicitly: `<= 0.0` alone would let NaN reach the score.
        if avg.partial_cmp(&0.0) != Some(Ordering::Greater)
            || x.partial_cmp(&0.0) != Some(Ordering::Greater)
        {
            return 0.0;
        }
        let r = x / avg;
        r / (1.0 + r)
    }

    /// The blended non-pseudocost signal for (`j`, `up`), in `[0, 1)`.
    ///
    /// Normalisation is over the signals that HAVE data for this column, not
    /// over both unconditionally: on an instance where node propagation never
    /// arms, `infer_cnt` is 0 for every column, and dividing by `w_inf + w_cut`
    /// would halve every column's bonus identically — a pure rescale of `w`
    /// masquerading as a signal. Over the available set the term keeps its
    /// meaning on both kinds of instance.
    pub(super) fn bonus(&self, j: usize, up: bool) -> f64 {
        let k = HybridHist::slot(j, up);
        if k >= self.h.visits.len() {
            return 0.0;
        }
        let (mut num, mut den) = (0.0, 0.0);
        if self.w_inf > 0.0 && self.h.infer_cnt[k] > 0 {
            let x = self.h.infer_sum[k] / self.h.infer_cnt[k] as f64;
            num += self.w_inf * Self::norm(x, self.inf_avg);
            den += self.w_inf;
        }
        if self.w_cut > 0.0 && self.h.visits[k] > 0 {
            let v = self.h.visits[k];
            let x = f64::from(v - self.h.branched[k].min(v)) / f64::from(v);
            num += self.w_cut * Self::norm(x, self.cut_avg);
            den += self.w_cut;
        }
        if den > 0.0 {
            num / den
        } else {
            0.0
        }
    }

    /// The multiplier applied to ONE side's pseudocost gain.
    ///
    /// PSEUDOCOST-DOMINANCE IS STRUCTURAL, not a weight choice: `unrel` ramps
    /// linearly from 1 at zero observations to 0 at `rel` of them, so a side the
    /// search already trusts gets the factor `1.0` — and `x * 1.0 == x` exactly
    /// in f64, which is why a mature column's score is BIT-IDENTICAL to the
    /// shipped rule. The hybrid term can only rearrange the band the shipped
    /// rule scores off a single noisy sample (or off the global average).
    pub(super) fn factor(&self, j: usize, up: bool, cnt: u32) -> f64 {
        let unrel = 1.0 - (f64::from(cnt) / self.rel).min(1.0);
        if unrel <= 0.0 {
            return 1.0;
        }
        let b = self.bonus(j, up);
        if b <= 0.0 {
            return 1.0;
        }
        1.0 + self.w * unrel * b
    }
}
