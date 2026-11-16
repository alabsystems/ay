// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `SpacerCoreStats` — the Workstream B board counters (`DESIGN` §4.6, §8.3,
//! contract C7). Owner: **WP-B1-L** defines the counters and the lane's
//! `record_q1` / `record_lemma`; **WP-B1-S** wires the struct into
//! `SolverStats`, the `--trace-file` telemetry block (`"spacer": {..}` under
//! `counters`), the per-lemma `LearnLemma` trace line and the `PDR-SPACER:`
//! verbose summary, and fills the R0 (legacy-path) recorders here so the
//! BEFORE board is produced by the same code that measures every later rung.
//!
//! Telemetry only: nothing in this struct is read by a verdict path.

#![allow(dead_code, unused)]

use crate::pdr::cube::literals::LitCube;
use crate::pdr::frame::Lemma;
use crate::pdr::solver::ProofObligation;
use crate::{ChcExpr, ChcOp, ChcVar};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::time::Duration;

use super::oracle::Budget;

/// Exact-value histogram for small non-negative integers (literal counts,
/// core sizes, milliseconds); values above `CAP` are clamped into the last bin.
#[derive(Debug, Clone)]
pub(in crate::pdr::solver) struct Hist {
    bins: Vec<u32>,
    count: u64,
    sum: u64,
    max: usize,
}

impl Hist {
    const CAP: usize = 2048;

    pub(in crate::pdr::solver) fn new() -> Self {
        Self {
            bins: Vec::new(),
            count: 0,
            sum: 0,
            max: 0,
        }
    }

    pub(in crate::pdr::solver) fn add(&mut self, v: usize) {
        if self.bins.is_empty() {
            self.bins = vec![0; Self::CAP + 1];
        }
        let i = v.min(Self::CAP);
        self.bins[i] = self.bins[i].saturating_add(1);
        self.count += 1;
        self.sum += v as u64;
        self.max = self.max.max(v);
    }

    pub(in crate::pdr::solver) fn count(&self) -> u64 {
        self.count
    }

    pub(in crate::pdr::solver) fn mean(&self) -> f64 {
        if self.count == 0 {
            0.0
        } else {
            self.sum as f64 / self.count as f64
        }
    }

    /// The `q`-quantile (0..=1) of the recorded values (`None` when empty).
    pub(in crate::pdr::solver) fn quantile(&self, q: f64) -> Option<usize> {
        if self.count == 0 {
            return None;
        }
        let target = ((self.count as f64) * q).ceil().max(1.0) as u64;
        let mut acc = 0u64;
        for (v, n) in self.bins.iter().enumerate() {
            acc += u64::from(*n);
            if acc >= target {
                return Some(v);
            }
        }
        Some(self.max)
    }

    pub(in crate::pdr::solver) fn json(&self) -> serde_json::Value {
        let hist: serde_json::Map<String, serde_json::Value> = self
            .bins
            .iter()
            .enumerate()
            .filter(|(_, n)| **n > 0)
            .map(|(v, n)| (v.to_string(), serde_json::json!(n)))
            .collect();
        serde_json::json!({
            "count": self.count,
            "sum": self.sum,
            "max": self.max,
            "mean": self.mean(),
            "p50": self.quantile(0.5),
            "p90": self.quantile(0.9),
            "hist": hist,
        })
    }
}

impl Default for Hist {
    fn default() -> Self {
        Self::new()
    }
}

/// Where a child cube came from (`DESIGN` §4.6 `cube_source`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(in crate::pdr::solver) enum CubeSource {
    /// R2 free implicant/MBP cube.
    MbpFree,
    /// R2 free cube that projected to `true` (empty `LitCube`).
    MbpFreeTrue,
    /// R2 per-variable model substitution for `k` residual variables (`k` in the histogram).
    PerVarSubst,
    /// Point-cube fallback: a residual variable had no usable model value.
    PointFallbackNoValue,
    /// Point-cube fallback: non-canonical residue.
    PointFallbackNonCanonical,
    /// Point-cube fallback: `eval_bool` model mismatch.
    PointFallbackMismatch,
    /// The legacy `cube_with_mbp` / array-aware constructor.
    Legacy,
}

/// Where a Q1 core came from (`DESIGN` §4.6 `q1_core_source`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(in crate::pdr::solver) enum Q1CoreSource {
    Proxied,
    Session,
    /// `propagate_equalities() == false` shortcut (all-true inexact).
    PropagateFalse,
    /// Background alone UNSAT: plain `Unsat`, activation-only core or the
    /// assumption solver's equality-closure contradiction path (the empty
    /// exact core).
    Contradiction,
    /// No core source (LRA / Unknown / legacy path).
    None,
}

/// How a lemma was produced (legacy attribution at R0; lane phases from R1).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(in crate::pdr::solver) enum LemmaSource {
    /// Legacy: interpolation cascade (any strategy).
    Cascade,
    /// Legacy: template ladder / heuristic generalisation.
    Template,
    /// Legacy: IUC shrink.
    Iuc,
    /// Legacy: point-blocking fallback.
    PointBlock,
    /// Legacy: `¬pob.state` (generalisation overshot).
    Original,
    /// Legacy: SCC joint strengthening.
    Scc,
    /// Legacy: convex-closure post-insertion lemma.
    ConvexClosure,
    /// Lane: `lemma_from_cores` (seed only, no drop).
    LaneSeed,
    /// Lane: `lemma_from_cores` after Phase B/D generalisation.
    LaneIndGen,
    /// Unknown / unattributed.
    Unknown,
}

impl LemmaSource {
    pub(in crate::pdr::solver) const fn as_str(self) -> &'static str {
        match self {
            Self::Cascade => "cascade",
            Self::Template => "template",
            Self::Iuc => "iuc",
            Self::PointBlock => "point_block",
            Self::Original => "original",
            Self::Scc => "scc",
            Self::ConvexClosure => "convex_closure",
            Self::LaneSeed => "lane_seed",
            Self::LaneIndGen => "lane_ind_gen",
            Self::Unknown => "unknown",
        }
    }
}

/// Class of a `BlockResult::Unknown` exit (`DESIGN` §4.6 `root_unknown_by_class`, lock L2).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(in crate::pdr::solver) enum UnknownClass {
    Cancelled,
    SmtUnknown,
    /// INV-L3: exclusion-dependent block (`q1_exclusion_dependent`).
    ExclusionDependent,
    /// Legacy lemma side (`verify_inductiveness_or_fallback`, cascade, …).
    LegacyLemma,
    /// `sat_no_cube` (a SAT clause whose cube extraction failed).
    SatNoCube,
    /// One of the two lifted enumeration exits (only when `lift_caps` is off).
    EnumerationCap,
    /// The lane's exclusion-free oracle has a model of the full cube although
    /// every Q1 was UNSAT (`q1_seed_refuted`; no lemma is minted).
    SeedRefuted,
    Other,
}

impl UnknownClass {
    pub(in crate::pdr::solver) const fn as_str(self) -> &'static str {
        match self {
            Self::Cancelled => "cancelled",
            Self::SmtUnknown => "smt_unknown",
            Self::ExclusionDependent => "exclusion_dependent",
            Self::LegacyLemma => "legacy_lemma",
            Self::SatNoCube => "sat_no_cube",
            Self::EnumerationCap => "enumeration_cap",
            Self::SeedRefuted => "seed_refuted",
            Self::Other => "other",
        }
    }
}

/// Snapshot of the most recently recorded POB (for the per-lemma trace line,
/// which is emitted from `lemma_mgmt.rs` where the POB is out of scope).
#[derive(Debug, Clone, Copy, Default)]
pub(in crate::pdr::solver) struct LastPob {
    pub lits: usize,
    pub point: bool,
    pub pins: usize,
    pub canon: usize,
    pub mentioned: usize,
    pub level: usize,
    pub predicate: usize,
}

/// The board counters (`DESIGN` §4.6). All `usize`/`Hist`; `Default` = zero.
#[derive(Debug, Clone, Default)]
pub(in crate::pdr::solver) struct SpacerCoreStats {
    // --- POB side ---
    pub pobs_processed: usize,
    pub pob_lits_hist: Hist,
    pub pob_point_cube: usize,
    pub pob_pin_density_sum: f64,
    pub pob_free_var_ratio_sum: f64,
    pub pob_true: usize,
    pub pob_disequalities: usize,
    pub pob_bool_eq_atoms: usize,
    pub pob_or_literal: usize,
    pub cube_source: FxHashMap<CubeSource, usize>,
    pub per_var_subst_hist: Hist,
    /// R2 exact-projection counters summed over free child cubes (WP-P, additive).
    pub mbp_exact: crate::mbp::exact::ExactStats,
    pub minimize_calls: usize,
    pub last_pob: LastPob,
    // --- blocking outcomes ---
    pub blocked_pobs: usize,
    pub reachable_pobs: usize,
    pub already_blocked_syntactic: usize,
    pub already_blocked_smt: usize,
    pub unknown_pobs: usize,
    pub root_unknown_by_class: FxHashMap<UnknownClass, usize>,
    pub child_unknown_by_class: FxHashMap<UnknownClass, usize>,
    // --- Q1 ---
    pub q1_calls: usize,
    pub q1_ite_leaves: usize,
    pub q1_core_source: FxHashMap<Q1CoreSource, usize>,
    pub q1_core_solve_ms_hist: Hist,
    pub q1_exclusion_dependent: usize,
    pub seed_core_size_hist: Hist,
    pub core_exact: usize,
    pub core_inexact: usize,
    pub core_confirm_checks: usize,
    pub core_confirm_disagree: usize,
    /// Confirmation checks that answered `Unknown` (a timeout, not a
    /// disagreement; the core is not adopted).
    pub core_confirm_unknown: usize,
    /// Blocks whose FULL cube is SAT under the exclusion-free Reach oracle
    /// although every Q1 answered UNSAT (untainted): the Q1 verdict is not
    /// reproducible by the oracle (expected 0 since the level-1 per-fact Q1
    /// renames fact variables apart under the lane; see `derive.rs` Phase 0).
    /// No lemma is minted (`DeriveError::SeedRefuted` ⇒ `Unknown`).
    pub q1_seed_refuted: usize,
    /// Lane derivation recorded by `record_lemma` and not yet consumed by the
    /// `record_legacy_lemma` call `strengthen` makes for the same lemma
    /// (keeps the lemma counted once, with the lane attribution).
    pub pending_lane_source: Option<LemmaSource>,
    // --- lemmas ---
    pub lemmas: usize,
    pub lemma_lits_hist: Hist,
    pub lemma_false: usize,
    pub lemma_diseq_lits: usize,
    pub lemma_source: FxHashMap<LemmaSource, usize>,
    pub drop_ratio_sum: f64,
    pub drop_ratio_count: usize,
    pub wide_pob_drop_ratio_sum: f64,
    pub wide_pob_drop_ratio_count: usize,
    // --- ind-gen ---
    pub ind_gen_queries_a: usize,
    pub ind_gen_queries_b: usize,
    pub ind_gen_queries_c: usize,
    pub ind_gen_queries_d: usize,
    pub q2_assume_unknown: usize,
    pub q2_fallback_verdict: usize,
    pub q2_ms_hist: Hist,
    pub ctp_skips: usize,
    pub ind_gen_unknown: usize,
    pub ind_gen_budget_hits: usize,
    pub level_climbs: usize,
    pub uses_level_jumps: usize,
    pub ind_gen_ms_total: u64,
    // --- exits / caps ---
    pub point_block_lemmas_per_level: FxHashMap<usize, usize>,
    pub point_block_cap_lifted: usize,
    pub level0_blocked: usize,
    pub level0_cap_lifted: usize,
    pub pob_no_progress: usize,
    pub sat_no_cube: usize,
    pub cex_concretize_ok: usize,
    pub cex_concretize_fail_unsat: usize,
    pub cex_concretize_fail_unknown: usize,
    pub cex_concretize_hyperedge: usize,
    pub lane_bypassed_arrays: usize,
    pub lane_bypassed_bv: usize,
    pub lane_bypassed_dt: usize,
    pub lane_bypassed_hyperedge: usize,
    pub lane_bypassed_nonlinear: usize,
    pub constructions_with_lane_in_validator: usize,
    /// Every `check_sat*` / assumption solve issued by the lane.
    pub smt_solves_total: usize,
    pub scc_solves: usize,
    /// Wall time spent in `block_obligation_with_local_blocked` (ms).
    pub block_ms_total: u64,
    // --- nonlinear lane (`lane_nonlinear`) ---
    /// Multi-atom predecessor queries (every clause with a body, facts at level ≥ 1).
    pub nl_q1: usize,
    /// ... of which answered SAT.
    pub nl_q1_sat: usize,
    /// Must-extension queries (`query ∧ pins ∧ RF(atom)`), and how many were SAT.
    pub nl_must_ext: usize,
    pub nl_must_ext_sat: usize,
    /// Reach facts recorded by the lane (facts, and clause steps whose atoms
    /// were all covered).
    pub nl_reach_facts: usize,
    /// POBs closed as reachable (`BlockResult::MustReachable`).
    pub nl_must_reachable: usize,
    /// Child POBs created for an uncovered body atom.
    pub nl_children: usize,
    /// A covered step whose completed model did not evaluate the step (no reach
    /// fact, the POB answers Unknown).
    pub nl_rf_fail: usize,
    /// Counterexample trees built from reach facts (root POB reachable).
    pub nl_cex: usize,
}

impl SpacerCoreStats {
    /// Record one popped POB (`strengthen.rs`, after the verbose "Processing obligation" line).
    ///
    /// `canon` = the predicate's canonical variables (`None` ⇒ point/pin/free
    /// metrics are skipped for this POB).
    pub(in crate::pdr::solver) fn record_pob(
        &mut self,
        pob: &ProofObligation,
        cube: &LitCube,
        canon: Option<&[ChcVar]>,
    ) {
        self.pobs_processed += 1;
        let n = cube.len();
        self.pob_lits_hist.add(n);
        if cube.is_empty() {
            self.pob_true += 1;
        }
        self.pob_disequalities += cube.diseq_count();
        let mut last = LastPob {
            lits: n,
            level: pob.level,
            predicate: pob.predicate.index(),
            ..LastPob::default()
        };
        if let Some(canon) = canon {
            let point = cube.is_point_cube(canon);
            if point {
                self.pob_point_cube += 1;
            }
            let pins = cube.pin_count();
            let mentioned = cube.mentioned_canon(canon);
            if n > 0 {
                self.pob_pin_density_sum += pins as f64 / n as f64;
            }
            if !canon.is_empty() {
                self.pob_free_var_ratio_sum +=
                    (canon.len().saturating_sub(mentioned)) as f64 / canon.len() as f64;
            }
            last.point = point;
            last.pins = pins;
            last.canon = canon.len();
            last.mentioned = mentioned;
        }
        for lit in cube.lits() {
            match lit {
                ChcExpr::Op(ChcOp::Or, _) => self.pob_or_literal += 1,
                ChcExpr::Op(ChcOp::Eq, args)
                    if args.len() == 2
                        && (matches!(&*args[0], ChcExpr::Op(ChcOp::Eq, _))
                            || matches!(&*args[1], ChcExpr::Op(ChcOp::Eq, _))) =>
                {
                    self.pob_bool_eq_atoms += 1;
                }
                _ => {}
            }
        }
        self.last_pob = last;
    }

    /// Record a child cube's source (R2 constructor / legacy).
    pub(in crate::pdr::solver) fn record_cube_source(&mut self, source: CubeSource, k: usize) {
        *self.cube_source.entry(source).or_insert(0) += 1;
        if source == CubeSource::PerVarSubst {
            self.per_var_subst_hist.add(k);
        }
    }

    /// Record a free child cube (R2): its source, substituted-variable count
    /// and the exact projector's counters (WP-P, additive).
    pub(in crate::pdr::solver) fn record_free_child(
        &mut self,
        source: CubeSource,
        k: usize,
        exact: &crate::mbp::exact::ExactStats,
    ) {
        self.record_cube_source(source, k);
        let m = &mut self.mbp_exact;
        m.unit_eq += exact.unit_eq;
        m.nonunit_eq += exact.nonunit_eq;
        m.bj_bounds += exact.bj_bounds;
        m.lw_bounds += exact.lw_bounds;
        m.one_sided += exact.one_sided;
        m.diseq_splits += exact.diseq_splits;
        m.ite_splits += exact.ite_splits;
        m.div_literals += exact.div_literals;
        m.bool_defs += exact.bool_defs;
    }

    /// Record one Q1 (`Hyp::Reach`) verdict solve and its core source (L, C7).
    pub(in crate::pdr::solver) fn record_q1(
        &mut self,
        source: Q1CoreSource,
        core_size: Option<usize>,
        exact: bool,
        core_solve: Option<Duration>,
        ite_leaves: usize,
    ) {
        self.q1_calls += 1;
        self.q1_ite_leaves += ite_leaves;
        *self.q1_core_source.entry(source).or_insert(0) += 1;
        if let Some(k) = core_size {
            self.seed_core_size_hist.add(k);
        }
        if exact {
            self.core_exact += 1;
        } else {
            self.core_inexact += 1;
        }
        if let Some(d) = core_solve {
            self.q1_core_solve_ms_hist
                .add(usize::try_from(d.as_millis()).unwrap_or(usize::MAX));
        }
        // `smt_solves_total` is counted at the solve sites (the proxied
        // assumption solve / the split verdict), not here: a Q1 record
        // without a solve (propagate shortcut, LRA) issues none.
    }

    /// Record a lane lemma (`lemma_from_cores`, §4.2.3): `full` = the POB
    /// cube, `cube` = the surviving sub-cube, `lvl` = the lemma's level.
    ///
    /// The lemma COUNT and shape are recorded once, by the
    /// `record_legacy_lemma` call `strengthen` makes for every `Blocked`
    /// lemma; this method records the lane-only fields (drop ratio, level
    /// climb, budget) and parks the lane attribution for that call.
    pub(in crate::pdr::solver) fn record_lemma(
        &mut self,
        pob: &ProofObligation,
        full: &LitCube,
        cube: &LitCube,
        lvl: usize,
        budget: &Budget,
    ) {
        let source = if cube.len() < full.len() || lvl > pob.level {
            LemmaSource::LaneIndGen
        } else {
            LemmaSource::LaneSeed
        };
        self.pending_lane_source = Some(source);
        if !full.is_empty() {
            let ratio = 1.0 - (cube.len() as f64 / full.len() as f64);
            self.drop_ratio_sum += ratio;
            self.drop_ratio_count += 1;
            if full.len() > 30 {
                self.wide_pob_drop_ratio_sum += ratio;
                self.wide_pob_drop_ratio_count += 1;
            }
        }
        if lvl > pob.level {
            self.level_climbs += 1;
        }
        if budget.exhausted() {
            self.ind_gen_budget_hits += 1;
        }
    }

    /// Record a legacy-path lemma (R0 attribution; S wires from `strengthen.rs`).
    /// `lemma.formula` is `Not(cube)`; the cube's literal count is measured.
    ///
    /// When a lane derivation is pending (`record_lemma` ran for this lemma),
    /// the lane attribution wins and the drop ratio is not counted twice.
    pub(in crate::pdr::solver) fn record_legacy_lemma(
        &mut self,
        lemma: &Lemma,
        source: LemmaSource,
    ) {
        let cube = match &lemma.formula {
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => LitCube::from_expr(&args[0]),
            ChcExpr::Bool(false) => LitCube::from_lits(Vec::new()),
            other => LitCube::from_lits(vec![ChcExpr::not(other.clone())]),
        };
        let is_false = matches!(lemma.formula, ChcExpr::Bool(false));
        if let Some(lane_source) = self.pending_lane_source.take() {
            self.note_lemma_shape(cube.len(), is_false, cube.diseq_count(), lane_source);
            return;
        }
        self.note_lemma_shape(cube.len(), is_false, cube.diseq_count(), source);
        let full = self.last_pob.lits;
        if full > 0 {
            let ratio = 1.0 - (cube.len().min(full) as f64 / full as f64);
            self.drop_ratio_sum += ratio;
            self.drop_ratio_count += 1;
            if full > 30 {
                self.wide_pob_drop_ratio_sum += ratio;
                self.wide_pob_drop_ratio_count += 1;
            }
        }
    }

    fn note_lemma_shape(&mut self, lits: usize, is_false: bool, diseq: usize, source: LemmaSource) {
        self.lemmas += 1;
        self.lemma_lits_hist.add(lits);
        if is_false {
            self.lemma_false += 1;
        }
        self.lemma_diseq_lits += diseq;
        *self.lemma_source.entry(source).or_insert(0) += 1;
    }

    /// Record a `BlockResult::Unknown` exit; `root` = the POB had no parent.
    pub(in crate::pdr::solver) fn record_unknown(&mut self, class: UnknownClass, root: bool) {
        self.unknown_pobs += 1;
        let map = if root {
            &mut self.root_unknown_by_class
        } else {
            &mut self.child_unknown_by_class
        };
        *map.entry(class).or_insert(0) += 1;
    }

    /// Record a point-block lemma at `level` (the lifted cap's counter).
    pub(in crate::pdr::solver) fn note_point_block(&mut self, level: usize) {
        *self.point_block_lemmas_per_level.entry(level).or_insert(0) += 1;
    }

    /// Lemmas per blocked POB (the om1 0.18 → 1.0 metric).
    pub(in crate::pdr::solver) fn lemmas_per_blocked_pob(&self) -> f64 {
        if self.blocked_pobs == 0 {
            0.0
        } else {
            self.lemmas as f64 / self.blocked_pobs as f64
        }
    }

    pub(in crate::pdr::solver) fn point_cube_share(&self) -> f64 {
        if self.pobs_processed == 0 {
            0.0
        } else {
            self.pob_point_cube as f64 / self.pobs_processed as f64
        }
    }

    pub(in crate::pdr::solver) fn pin_density(&self) -> f64 {
        if self.pobs_processed == 0 {
            0.0
        } else {
            self.pob_pin_density_sum / self.pobs_processed as f64
        }
    }

    pub(in crate::pdr::solver) fn free_var_ratio(&self) -> f64 {
        if self.pobs_processed == 0 {
            0.0
        } else {
            self.pob_free_var_ratio_sum / self.pobs_processed as f64
        }
    }

    pub(in crate::pdr::solver) fn core_exact_share(&self) -> Option<f64> {
        let n = self.core_exact + self.core_inexact;
        if n == 0 {
            None
        } else {
            Some(self.core_exact as f64 / n as f64)
        }
    }

    pub(in crate::pdr::solver) fn drop_ratio(&self) -> Option<f64> {
        if self.drop_ratio_count == 0 {
            None
        } else {
            Some(self.drop_ratio_sum / self.drop_ratio_count as f64)
        }
    }

    fn map_json<K: Copy>(m: &FxHashMap<K, usize>, name: impl Fn(K) -> String) -> serde_json::Value {
        let mut entries: Vec<(String, usize)> = m.iter().map(|(k, v)| (name(*k), *v)).collect();
        entries.sort();
        serde_json::Value::Object(
            entries
                .into_iter()
                .map(|(k, v)| (k, serde_json::json!(v)))
                .collect(),
        )
    }

    /// The `"spacer": {..}` telemetry block (C7).
    pub(in crate::pdr::solver) fn json(&self) -> serde_json::Value {
        let q2_total = self.ind_gen_queries_b + self.ind_gen_queries_d;
        let mut m = serde_json::Map::new();
        let mut put = |k: &str, v: serde_json::Value| {
            m.insert(k.to_string(), v);
        };
        // POB side
        put("pobs_processed", serde_json::json!(self.pobs_processed));
        put("pob_lits", self.pob_lits_hist.json());
        put("pob_point_cube", serde_json::json!(self.pob_point_cube));
        put(
            "point_cube_share",
            serde_json::json!(self.point_cube_share()),
        );
        put("pin_density", serde_json::json!(self.pin_density()));
        put("free_var_ratio", serde_json::json!(self.free_var_ratio()));
        put("pob_true", serde_json::json!(self.pob_true));
        put(
            "pob_disequalities",
            serde_json::json!(self.pob_disequalities),
        );
        put(
            "pob_bool_eq_atoms",
            serde_json::json!(self.pob_bool_eq_atoms),
        );
        put("pob_or_literal", serde_json::json!(self.pob_or_literal));
        put(
            "cube_source",
            Self::map_json(&self.cube_source, |k| format!("{k:?}")),
        );
        put("per_var_subst", self.per_var_subst_hist.json());
        {
            let m = &self.mbp_exact;
            put(
                "mbp_exact",
                serde_json::json!({
                    "unit_eq": m.unit_eq, "nonunit_eq": m.nonunit_eq, "bj_bounds": m.bj_bounds,
                    "lw_bounds": m.lw_bounds, "one_sided": m.one_sided,
                    "diseq_splits": m.diseq_splits, "ite_splits": m.ite_splits,
                    "div_literals": m.div_literals, "bool_defs": m.bool_defs,
                }),
            );
        }
        put("minimize_calls", serde_json::json!(self.minimize_calls));
        // Blocking outcomes
        put("blocked_pobs", serde_json::json!(self.blocked_pobs));
        put("reachable_pobs", serde_json::json!(self.reachable_pobs));
        put(
            "already_blocked_syntactic",
            serde_json::json!(self.already_blocked_syntactic),
        );
        put(
            "already_blocked_smt",
            serde_json::json!(self.already_blocked_smt),
        );
        put("unknown_pobs", serde_json::json!(self.unknown_pobs));
        put(
            "root_unknown_by_class",
            Self::map_json(&self.root_unknown_by_class, |k| k.as_str().to_string()),
        );
        put(
            "child_unknown_by_class",
            Self::map_json(&self.child_unknown_by_class, |k| k.as_str().to_string()),
        );
        // Q1
        put("q1_calls", serde_json::json!(self.q1_calls));
        put("q1_ite_leaves", serde_json::json!(self.q1_ite_leaves));
        put(
            "q1_core_source",
            Self::map_json(&self.q1_core_source, |k| format!("{k:?}")),
        );
        put("q1_core_solve_ms", self.q1_core_solve_ms_hist.json());
        put(
            "q1_exclusion_dependent",
            serde_json::json!(self.q1_exclusion_dependent),
        );
        put("seed_core_size", self.seed_core_size_hist.json());
        put(
            "core_exact_share",
            serde_json::json!(self.core_exact_share()),
        );
        put(
            "core_confirm_checks",
            serde_json::json!(self.core_confirm_checks),
        );
        put(
            "core_confirm_disagree",
            serde_json::json!(self.core_confirm_disagree),
        );
        put(
            "core_confirm_unknown",
            serde_json::json!(self.core_confirm_unknown),
        );
        put("q1_seed_refuted", serde_json::json!(self.q1_seed_refuted));
        // Lemmas
        put("lemmas", serde_json::json!(self.lemmas));
        put(
            "lemmas_per_blocked_pob",
            serde_json::json!(self.lemmas_per_blocked_pob()),
        );
        put("lemma_lits", self.lemma_lits_hist.json());
        put("lemma_false", serde_json::json!(self.lemma_false));
        put("lemma_diseq_lits", serde_json::json!(self.lemma_diseq_lits));
        put(
            "lemma_source",
            Self::map_json(&self.lemma_source, |k| k.as_str().to_string()),
        );
        put("drop_ratio", serde_json::json!(self.drop_ratio()));
        let wide = if self.wide_pob_drop_ratio_count == 0 {
            None
        } else {
            Some(self.wide_pob_drop_ratio_sum / self.wide_pob_drop_ratio_count as f64)
        };
        put("wide_pob_drop_ratio", serde_json::json!(wide));
        // Ind-gen
        put(
            "ind_gen_queries",
            serde_json::json!({"a": self.ind_gen_queries_a, "b": self.ind_gen_queries_b, "c": self.ind_gen_queries_c, "d": self.ind_gen_queries_d}),
        );
        put(
            "q2_assume_unknown",
            serde_json::json!(self.q2_assume_unknown),
        );
        let q2_share = if q2_total == 0 {
            None
        } else {
            Some(self.q2_assume_unknown as f64 / q2_total as f64)
        };
        put("q2_assume_unknown_share", serde_json::json!(q2_share));
        put(
            "q2_fallback_verdict",
            serde_json::json!(self.q2_fallback_verdict),
        );
        put("q2_ms", self.q2_ms_hist.json());
        put("ctp_skips", serde_json::json!(self.ctp_skips));
        put("ind_gen_unknown", serde_json::json!(self.ind_gen_unknown));
        put(
            "ind_gen_budget_hits",
            serde_json::json!(self.ind_gen_budget_hits),
        );
        put("ind_gen_ms_total", serde_json::json!(self.ind_gen_ms_total));
        put("level_climbs", serde_json::json!(self.level_climbs));
        put("uses_level_jumps", serde_json::json!(self.uses_level_jumps));
        // Exits / caps
        put(
            "point_block_lemmas_per_level",
            Self::map_json(&self.point_block_lemmas_per_level, |k| k.to_string()),
        );
        put(
            "point_block_cap_lifted",
            serde_json::json!(self.point_block_cap_lifted),
        );
        put("level0_blocked", serde_json::json!(self.level0_blocked));
        put(
            "level0_cap_lifted",
            serde_json::json!(self.level0_cap_lifted),
        );
        put("pob_no_progress", serde_json::json!(self.pob_no_progress));
        put("sat_no_cube", serde_json::json!(self.sat_no_cube));
        put(
            "cex_concretize",
            serde_json::json!({"ok": self.cex_concretize_ok, "fail_unsat": self.cex_concretize_fail_unsat, "fail_unknown": self.cex_concretize_fail_unknown, "hyperedge": self.cex_concretize_hyperedge}),
        );
        put(
            "lane_bypassed",
            serde_json::json!({"arrays": self.lane_bypassed_arrays, "bv": self.lane_bypassed_bv, "dt": self.lane_bypassed_dt, "hyperedge": self.lane_bypassed_hyperedge, "nonlinear": self.lane_bypassed_nonlinear}),
        );
        put(
            "constructions_with_lane_in_validator",
            serde_json::json!(self.constructions_with_lane_in_validator),
        );
        put("smt_solves_total", serde_json::json!(self.smt_solves_total));
        put("scc_solves", serde_json::json!(self.scc_solves));
        put("block_ms_total", serde_json::json!(self.block_ms_total));
        put(
            "nonlinear",
            serde_json::json!({"q1": self.nl_q1, "q1_sat": self.nl_q1_sat, "must_ext": self.nl_must_ext, "must_ext_sat": self.nl_must_ext_sat, "reach_facts": self.nl_reach_facts, "must_reachable": self.nl_must_reachable, "children": self.nl_children, "rf_fail": self.nl_rf_fail, "cex": self.nl_cex}),
        );
        serde_json::Value::Object(m)
    }

    /// One-line `PDR-SPACER:` verbose summary.
    pub(in crate::pdr::solver) fn verbose_summary(&self) -> String {
        format!(
            "PDR-SPACER: pobs={} point_cube={:.2} pin_density={:.2} free_var_ratio={:.2} pob_lits_p50={} pob_lits_p90={} blocked={} reachable={} already_blocked={}+{} unknown={} lemmas={} lemmas/blocked={:.2} lemma_lits_p50={} lemma_lits_p90={} lemma_diseq={} lemma_false={} q1={} core_exact_share={} confirm_disagree={} smt_solves={} point_blocks={} level0_blocked={} sat_no_cube={} cex_concretize_fail={} nl_q1={}/{} nl_must_ext={}/{} nl_rf={} nl_reach={} nl_children={} nl_rf_fail={} nl_cex={}",
            self.pobs_processed,
            self.point_cube_share(),
            self.pin_density(),
            self.free_var_ratio(),
            self.pob_lits_hist.quantile(0.5).unwrap_or(0),
            self.pob_lits_hist.quantile(0.9).unwrap_or(0),
            self.blocked_pobs,
            self.reachable_pobs,
            self.already_blocked_syntactic,
            self.already_blocked_smt,
            self.unknown_pobs,
            self.lemmas,
            self.lemmas_per_blocked_pob(),
            self.lemma_lits_hist.quantile(0.5).unwrap_or(0),
            self.lemma_lits_hist.quantile(0.9).unwrap_or(0),
            self.lemma_diseq_lits,
            self.lemma_false,
            self.q1_calls,
            self.core_exact_share()
                .map_or_else(|| "n/a".to_string(), |v| format!("{v:.2}")),
            self.core_confirm_disagree,
            self.smt_solves_total,
            self.point_block_lemmas_per_level.values().sum::<usize>(),
            self.level0_blocked,
            self.sat_no_cube,
            self.cex_concretize_fail_unsat + self.cex_concretize_fail_unknown,
            self.nl_q1_sat,
            self.nl_q1,
            self.nl_must_ext_sat,
            self.nl_must_ext,
            self.nl_reach_facts,
            self.nl_must_reachable,
            self.nl_children,
            self.nl_rf_fail,
            self.nl_cex,
        )
    }
}
