// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Typed carriers for branch-and-bound engine lanes.

use crate::tune::Knob;

use super::{checked, EngineConfigError, EngineEconomics};

impl EngineEconomics {
    /// GUB/SOS1 branching. Default on (auto-armed on supports).
    #[must_use]
    pub fn with_gub_branch(mut self, enabled: bool) -> Self {
        self.gub_branch = Some(enabled);
        self
    }

    /// Duplicate-column presolve merging. Default on (optimum-preserving).
    #[must_use]
    pub fn with_dedup_cols(mut self, enabled: bool) -> Self {
        self.dedup_cols = Some(enabled);
        self
    }

    /// Binary equivalence/complement substitution. Default on.
    #[must_use]
    pub fn with_binary_complement_sub(mut self, enabled: bool) -> Self {
        self.binary_complement_sub = Some(enabled);
        self
    }

    /// Coldest-first no-good box replacement. Default on.
    #[must_use]
    pub fn with_lb_activity(mut self, enabled: bool) -> Self {
        self.lb_activity = Some(enabled);
        self
    }

    /// Depth-first routing for the pure general-integer shape. Default on.
    #[must_use]
    pub fn with_gi_dfs(mut self, enabled: bool) -> Self {
        self.gi_dfs = Some(enabled);
        self
    }

    /// Objective-cutoff-row propagation. Default on.
    #[must_use]
    pub fn with_impl_cut(mut self, enabled: bool) -> Self {
        self.impl_cut = Some(enabled);
        self
    }

    /// Mined-implication table pass. Default on.
    #[must_use]
    pub fn with_impl_tab(mut self, enabled: bool) -> Self {
        self.impl_tab = Some(enabled);
        self
    }

    /// Knapsack dry-ball narrow redirect. Default on.
    #[must_use]
    pub fn with_knap_redirect(mut self, enabled: bool) -> Self {
        self.knap_redirect = Some(enabled);
        self
    }

    /// Terminal-dive poison-column deferral. Default on.
    #[must_use]
    pub fn with_dive_skip(mut self, enabled: bool) -> Self {
        self.dive_skip = Some(enabled);
        self
    }

    /// Fused clone-free exact cut/LU accumulation. Default on;
    /// `with_cut_fma(false)` restores the literal clone form byte-for-byte.
    #[must_use]
    pub fn with_cut_fma(mut self, enabled: bool) -> Self {
        self.cut_fma = Some(enabled);
        self
    }

    /// Odd-hole cut lifting. Default on (the lifted row dominates).
    #[must_use]
    pub fn with_odd_lift(mut self, enabled: bool) -> Self {
        self.odd_lift = Some(enabled);
        self
    }

    /// Strong-CG separation. Default on.
    #[must_use]
    pub fn with_strongcg(mut self, enabled: bool) -> Self {
        self.strongcg = Some(enabled);
        self
    }

    /// Dense GMI basis rebuild (the pre-sparse path). Default OFF; opt-in
    /// measurement arm for the "identical cuts, less memory" claim.
    #[must_use]
    pub fn with_dense_gmi_lu(mut self, enabled: bool) -> Self {
        self.dense_gmi_lu = Some(enabled);
        self
    }

    /// Full pricing forced on big LPs. Default OFF (swept partial default).
    #[must_use]
    pub fn with_full_pricing(mut self, enabled: bool) -> Self {
        self.full_pricing = Some(enabled);
        self
    }

    /// Knapsack-form complementation beside the nearest-bound one in MIR /
    /// strong-CG row preparation. `Some(true)` forces it on beyond a moved
    /// default; `Some(false)` is the kill switch.
    #[must_use]
    pub fn with_mir_knap(mut self, enabled: bool) -> Self {
        self.mir_knap = Some(enabled);
        self
    }

    /// Opt-in bound-branch gate (B37; measured net-negative on its own gate).
    #[must_use]
    pub fn with_bound_branch(mut self, enabled: bool) -> Self {
        self.bound_branch = Some(enabled);
        self
    }

    /// Child-order force: `0` away, `1` up, `2` dn, `3` lp (B37; unset keeps
    /// the shape auto decision).
    pub fn with_child_order(mut self, mode: usize) -> Result<Self, EngineConfigError> {
        if mode > 3 {
            return Err(EngineConfigError::OutOfRange {
                knob: Knob::ChildOrderMode.label(),
                value: mode as f64,
                low: 0.0,
                high: 3.0,
            });
        }
        self.child_order = Some(mode);
        Ok(self)
    }

    /// Root cuts-per-round force (B37; unset keeps the shape-gated default).
    #[must_use]
    pub fn with_cuts_per_round(mut self, cuts: usize) -> Self {
        self.cuts_per_round = Some(cuts);
        self
    }

    /// Root cut-efficacy floor force (B37; `0` disables; unset keeps the
    /// aspect-ratio auto decision).
    pub fn with_cut_eff_floor(mut self, floor: f64) -> Result<Self, EngineConfigError> {
        if !floor.is_finite() || floor < 0.0 {
            return Err(EngineConfigError::OutOfRange {
                knob: Knob::CutEffFloor.label(),
                value: floor,
                low: 0.0,
                high: f64::MAX,
            });
        }
        self.cut_eff_floor = Some(floor);
        Ok(self)
    }

    /// Forrest-Tomlin spike arm force: `1` dense, `2` sparse (B37; unset
    /// keeps the measured auto rule).
    pub fn with_ft_spike(mut self, arm: usize) -> Result<Self, EngineConfigError> {
        if !(1..=2).contains(&arm) {
            return Err(EngineConfigError::OutOfRange {
                knob: Knob::FtSpikeArm.label(),
                value: arm as f64,
                low: 1.0,
                high: 2.0,
            });
        }
        self.ft_spike = Some(arm);
        Ok(self)
    }

    /// Strong GUB branching force (B37; unset = on iff wide).
    #[must_use]
    pub fn with_gub_sb(mut self, enabled: bool) -> Self {
        self.gub_sb = Some(enabled);
        self
    }

    /// Box no-good widening force (B37; unset = structural gate).
    #[must_use]
    pub fn with_ng_box(mut self, enabled: bool) -> Self {
        self.ng_box = Some(enabled);
        self
    }

    /// No-good branching band in percent (B37; `0` kills; unset = 25 iff
    /// ng_up armed).
    pub fn with_ng_branch_pct(mut self, pct: f64) -> Result<Self, EngineConfigError> {
        if !pct.is_finite() || pct < 0.0 {
            return Err(EngineConfigError::OutOfRange {
                knob: Knob::NgBranchPct.label(),
                value: pct,
                low: 0.0,
                high: f64::MAX,
            });
        }
        self.ng_branch_pct = Some(pct);
        Ok(self)
    }

    /// Branch-row propagation force (B37; unset = mixed-lever default).
    #[must_use]
    pub fn with_node_prop(mut self, enabled: bool) -> Self {
        self.node_prop = Some(enabled);
        self
    }

    /// Strong-branching sustain force (B37; unset = mixed-lever default).
    #[must_use]
    pub fn with_sb_sustain(mut self, enabled: bool) -> Self {
        self.sb_sustain = Some(enabled);
        self
    }

    /// Plunge-class arming (B37; unset = the qiu/mas74 structural classes).
    #[must_use]
    pub fn with_plunge(mut self, enabled: bool) -> Self {
        self.plunge = Some(enabled);
        self
    }

    /// Full GMI/MIR separation rounds at the root (B38; was --gmi-rounds).
    #[must_use]
    pub fn with_gmi_rounds(mut self, rounds: usize) -> Self {
        self.gmi_rounds = Some(rounds);
        self
    }

    /// Cuts retained per round at the root (B38).
    #[must_use]
    pub fn with_root_cuts_per_round(mut self, cuts: usize) -> Self {
        self.root_cuts_per_round = Some(cuts);
        self
    }

    /// Implication probing at the root (B38).
    #[must_use]
    pub fn with_root_probe(mut self, enabled: bool) -> Self {
        self.root_probe = Some(enabled);
        self
    }

    /// Depth-first node selection (B38).
    #[must_use]
    pub fn with_dfs(mut self, enabled: bool) -> Self {
        self.dfs = Some(enabled);
        self
    }

    /// Cut separation at nodes below the root (B38).
    #[must_use]
    pub fn with_node_cuts(mut self, enabled: bool) -> Self {
        self.node_cuts = Some(enabled);
        self
    }

    /// Symmetry-branch band force in `[0, 1]` (B39; out-of-domain reads as
    /// the tiebreak default).
    #[must_use]
    pub fn with_sym_branch_band(mut self, band: f64) -> Self {
        self.sym_branch_band = Some(band);
        self
    }

    /// Pin one RINS ladder arm: `1` pump, `2` submip, `3` fj (B39).
    pub fn with_rins_arm(mut self, arm: usize) -> Result<Self, EngineConfigError> {
        if !(1..=3).contains(&arm) {
            return Err(EngineConfigError::OutOfRange {
                knob: Knob::Rins.label(),
                value: arm as f64,
                low: 1.0,
                high: 3.0,
            });
        }
        self.rins = Some(arm);
        Ok(self)
    }

    /// Offer dual fixing on every model shape (B39 opt-in widening).
    #[must_use]
    pub fn with_dualfix_all(mut self, enabled: bool) -> Self {
        self.dualfix_all = Some(enabled);
        self
    }

    /// Implied-bound separator (B39 opt-in; measured to separate nothing on
    /// the corpus, kept as the sound separator a probing source would feed).
    #[must_use]
    pub fn with_implied_bound(mut self, enabled: bool) -> Self {
        self.implied_bound = Some(enabled);
        self
    }

    /// Lifted-cover separator (B39 opt-in; measured neutral).
    #[must_use]
    pub fn with_lifted_cover(mut self, enabled: bool) -> Self {
        self.lifted_cover = Some(enabled);
        self
    }

    /// Lift-and-project CGLP budget per root round; `0` disables (B39).
    #[must_use]
    pub fn with_lnp_budget(mut self, budget: usize) -> Self {
        self.lnp_budget = Some(budget);
        self
    }

    /// Lattice BKZ block-size override; `< 3` selects plain LLL (B39).
    #[must_use]
    pub fn with_lattice_bkz_beta(mut self, beta: usize) -> Self {
        self.lattice_bkz_beta = Some(beta);
        self
    }

    /// Dual cost-perturbation magnitude; `0` (the default) is off (B39).
    #[must_use]
    pub fn with_dual_perturb(mut self, magnitude: f64) -> Self {
        self.dual_perturb = Some(magnitude);
        self
    }

    /// Certificate grace budget in seconds; `0` selects uncapped (B39).
    #[must_use]
    pub fn with_cert_grace_secs(mut self, secs: f64) -> Self {
        self.cert_grace_secs = Some(secs);
        self
    }

    /// Anchor first-refusal window in milliseconds; `0` disables deferral
    /// (B39).
    #[must_use]
    pub fn with_anchor_first_refusal_ms(mut self, ms: usize) -> Self {
        self.anchor_first_refusal_ms = Some(ms);
        self
    }

    /// RINS cadence base, in nodes (B39b; `0` is nonsense and reads as the
    /// tuned default).
    #[must_use]
    pub fn with_rins_every(mut self, nodes: usize) -> Self {
        self.rins_every = Some(nodes);
        self
    }

    /// RINS wide-gap dry-spell cap; `0` disables the backoff (B39b).
    #[must_use]
    pub fn with_rins_drycap(mut self, cap: usize) -> Self {
        self.rins_drycap = Some(cap);
        self
    }

    /// Pin the feasibility-pump share (bypasses the work cap; B39b).
    #[must_use]
    pub fn with_pump_share(mut self, share: f64) -> Self {
        self.pump_share = Some(share);
        self
    }

    /// Pin the set-partition constructor share in `[0, 1]` (B39b).
    #[must_use]
    pub fn with_setpart_share(mut self, share: f64) -> Self {
        self.setpart_share = Some(share);
        self
    }

    /// Enlight-parity exact route (B39b; default on).
    #[must_use]
    pub fn with_parity(mut self, enabled: bool) -> Self {
        self.parity = Some(enabled);
        self
    }

    /// Margin reframing (B39b; default on).
    #[must_use]
    pub fn with_margin_reframe(mut self, enabled: bool) -> Self {
        self.margin_reframe = Some(enabled);
        self
    }

    /// Symmetry handling mode: `0` orbital (default), `1` rows, `2` off
    /// (B39b).
    pub fn with_sym_mode(mut self, mode: usize) -> Result<Self, EngineConfigError> {
        if mode > 2 {
            return Err(EngineConfigError::OutOfRange {
                knob: Knob::SymMode.label(),
                value: mode as f64,
                low: 0.0,
                high: 2.0,
            });
        }
        self.sym_mode = Some(mode);
        Ok(self)
    }

    /// Pin the root heuristic share (B39b; unset = shape-dependent default).
    #[must_use]
    pub fn with_heur_share(mut self, share: f64) -> Self {
        self.heur_share = Some(share);
        self
    }

    /// Strong-branching reliability threshold force (B39c).
    #[must_use]
    pub fn with_sb_rel(mut self, rel: usize) -> Self {
        self.sb_rel = Some(rel);
        self
    }

    /// Strong-branching candidate count force (B39c).
    #[must_use]
    pub fn with_sb_cands(mut self, cands: usize) -> Self {
        self.sb_cands = Some(cands);
        self
    }

    /// Strong-branching total probe budget pin (B39c).
    #[must_use]
    pub fn with_sb_total(mut self, total: usize) -> Self {
        self.sb_total = Some(total);
        self
    }

    /// Presolve (B39c; default on).
    #[must_use]
    pub fn with_presolve(mut self, enabled: bool) -> Self {
        self.presolve = Some(enabled);
        self
    }

    /// Presolve scout plan (B39c; default on).
    #[must_use]
    pub fn with_presolve_scout(mut self, enabled: bool) -> Self {
        self.presolve_scout = Some(enabled);
        self
    }

    /// VSIDS branching force (B39c; unset = the feasibility-class gate).
    #[must_use]
    pub fn with_vsids(mut self, enabled: bool) -> Self {
        self.vsids = Some(enabled);
        self
    }

    /// Probe every binary at the root (B39c opt-in widening).
    #[must_use]
    pub fn with_root_probe_all(mut self, enabled: bool) -> Self {
        self.root_probe_all = Some(enabled);
        self
    }

    /// Separation-statistics census dump (B40 diagnostic).
    #[must_use]
    pub fn with_sepstat(mut self, enabled: bool) -> Self {
        self.sepstat = Some(enabled);
        self
    }

    /// Run the root-closure diagnostic on the presolve-tightened model — the
    /// model the SEARCH actually hands its cut loop — instead of the raw file.
    /// Measurement-only: the diagnostic knob existed but had no typed carrier,
    /// so it was unreachable from the harness CLIs (W-safenlp-1).
    #[must_use]
    pub fn with_root_closure_presolve(mut self, enabled: bool) -> Self {
        self.root_closure_presolve = Some(enabled);
        self
    }

    /// Float-BTRAN tableau MIR in the root cut loop (opt-in measurement arm).
    #[must_use]
    pub fn with_tableau_mir(mut self, enabled: bool) -> Self {
        self.tableau_mir = Some(enabled);
        self
    }

    /// Admit aggregated MIR (`separate_mir_agg`) into every MIR-class root round
    /// (the measurement arm for the aggregation family; stage-two extension
    /// rounds are unreachable on the shapes it was written for).
    #[must_use]
    pub fn with_mir_agg_root(mut self, enabled: bool) -> Self {
        self.mir_agg_root = Some(enabled);
        self
    }

    /// Per-solve LP statistics line (B40 diagnostic).
    #[must_use]
    pub fn with_lp_stats(mut self, enabled: bool) -> Self {
        self.lp_stats = Some(enabled);
        self
    }

    /// Trace the first `n` simplex steps (B40 diagnostic).
    #[must_use]
    pub fn with_step_trace(mut self, n: usize) -> Self {
        self.step_trace = Some(n);
        self
    }

    /// BUMP-LU factor diagnostics (B40 diagnostic).
    #[must_use]
    pub fn with_bump_diag(mut self, enabled: bool) -> Self {
        self.bump_diag = Some(enabled);
        self
    }

    /// bumpdiff lane pair, lanes `0..=2`, `a != b` (B40 diagnostic).
    pub fn with_bumpdiff_lanes(mut self, a: usize, b: usize) -> Result<Self, EngineConfigError> {
        if a > 2 || b > 2 || a == b {
            return Err(EngineConfigError::OutOfRange {
                knob: Knob::BumpdiffLanes.label(),
                value: (a * 10 + b) as f64,
                low: 0.0,
                high: 21.0,
            });
        }
        self.bumpdiff_lanes = Some(a * 10 + b);
        Ok(self)
    }

    /// Plain-cold LP diagnostic arm (B40 diagnostic).
    #[must_use]
    pub fn with_diag_plain_cold(mut self, enabled: bool) -> Self {
        self.diag_plain_cold = Some(enabled);
        self
    }

    /// Root vertex dump (B40 diagnostic).
    #[must_use]
    pub fn with_dump_vertex(mut self, enabled: bool) -> Self {
        self.dump_vertex = Some(enabled);
        self
    }

    /// MEASUREMENT-ONLY node cap (B48; was a retired never-set env
    /// override): stop the tree after `n` processed nodes with the
    /// interrupted-but-valid Feasible/dual-bound outcome.
    #[must_use]
    pub fn with_max_nodes(mut self, n: usize) -> Self {
        self.max_nodes = Some(n);
        self
    }

    /// Opt in to the structure-attack elimination arm (B49).
    #[must_use]
    pub fn with_struct_elim(mut self, enabled: bool) -> Self {
        self.struct_elim = Some(enabled);
        self
    }

    /// Enable/disable the dual-bound cover pass (B49; default on).
    #[must_use]
    pub fn with_bound_cover(mut self, enabled: bool) -> Self {
        self.bound_cover = Some(enabled);
        self
    }

    /// Pin the feasibility-pump iteration-cap multiplier (B49).
    #[must_use]
    pub fn with_pump_iter_mult(mut self, mult: f64) -> Self {
        self.pump_iter_mult = Some(mult);
        self
    }

    /// Enable/disable the pump iteration cap (B49; default on).
    #[must_use]
    pub fn with_pump_iter_cap(mut self, enabled: bool) -> Self {
        self.pump_iter_cap = Some(enabled);
        self
    }

    /// Pin nogood upward propagation off/force (B49; unset = auto arm).
    #[must_use]
    pub fn with_ng_up(mut self, force: bool) -> Self {
        self.ng_up = Some(force);
        self
    }

    /// Cut-shadow audit mode: 1 = binding, 2 = slack (B49).
    #[must_use]
    pub fn with_cut_shadow(mut self, mode: u8) -> Self {
        self.cut_shadow = Some(mode);
        self
    }

    /// Opt in to MIR chain aggregation (B49).
    #[must_use]
    pub fn with_chain_agg(mut self, enabled: bool) -> Self {
        self.chain_agg = Some(enabled);
        self
    }

    /// Opt in to automatic margin-row detection (B49).
    #[must_use]
    pub fn with_auto_margin(mut self, enabled: bool) -> Self {
        self.auto_margin = Some(enabled);
        self
    }

    /// Pin the implication lane off/force (B50; unset = class auto).
    #[must_use]
    pub fn with_impl_lane(mut self, force: bool) -> Self {
        self.impl_lane = Some(force);
        self
    }

    /// Override the implication-lane arming node (B50).
    #[must_use]
    pub fn with_impl_arm(mut self, node: usize) -> Self {
        self.impl_arm = Some(node);
        self
    }

    /// Leaf-drought plunge cadence/arming override (the 80-binary zero-leaves
    /// fix; journal at `drought_class` in `bab.rs`). `0` kills the lane; `n`
    /// arms it at node `n` with one dive per `n` pops; unset = the shipped
    /// constants.
    #[must_use]
    pub fn with_drought_dive(mut self, n: usize) -> Self {
        self.drought_dive = Some(n);
        self
    }

    /// Pin propagation-conflict learning off/force (B50; unset = auto).
    #[must_use]
    pub fn with_prop_conflict(mut self, force: bool) -> Self {
        self.prop_conflict = Some(force);
        self
    }

    /// Bound-prune conflict learning: 1 = class, 2 = force (B50).
    #[must_use]
    pub fn with_lb_conflict(mut self, mode: u8) -> Self {
        self.lb_conflict = Some(mode);
        self
    }

    /// Override the bound-prune learning arming node (B50).
    #[must_use]
    pub fn with_lb_arm(mut self, node: usize) -> Self {
        self.lb_arm = Some(node);
        self
    }

    /// Strict bound-prune admission (B50; default true).
    #[must_use]
    pub fn with_lb_strict(mut self, strict: bool) -> Self {
        self.lb_strict = Some(strict);
        self
    }

    /// External dual bound delivered as a cutoff, in the MODEL objective
    /// frame (B71; the mps_solve example maps file-frame values in).
    #[must_use]
    pub fn with_dual_cutoff(mut self, cutoff: f64) -> Self {
        self.dual_cutoff = Some(cutoff);
        self
    }

    /// Force the ay-dpll SMT lowering lane instead of native branch-and-bound
    /// (B40b A/B lever).
    #[must_use]
    pub fn with_smt_lane(mut self, enabled: bool) -> Self {
        self.smt_lane = Some(enabled);
        self
    }

    /// Aggregated flow-cover side pool. Default on.
    #[must_use]
    pub fn with_flowcover_agg(mut self, enabled: bool) -> Self {
        self.flowcover_agg = Some(enabled);
        self
    }

    /// General-integer GMI extension rounds. Default on (auto-gated).
    #[must_use]
    pub fn with_gi_ext(mut self, enabled: bool) -> Self {
        self.gi_ext = Some(enabled);
        self
    }

    /// Small-symmetric-bottleneck GMI extension. Default on (auto-gated).
    #[must_use]
    pub fn with_bottleneck_ext(mut self, enabled: bool) -> Self {
        self.bottleneck_ext = Some(enabled);
        self
    }

    /// Clique separation. Default on.
    #[must_use]
    pub fn with_clique(mut self, enabled: bool) -> Self {
        self.clique = Some(enabled);
        self
    }

    /// Lifted odd-hole separation: `Some(false)` disables it everywhere,
    /// `Some(true)` forces it beyond the wide-set-partition auto-arm.
    #[must_use]
    pub fn with_odd_cycle(mut self, enabled: bool) -> Self {
        if enabled {
            self.odd_cycle_on = Some(true);
        } else {
            self.odd_cycle_off = Some(true);
        }
        self
    }

    /// Cover-bought extended separation rounds. Default on.
    #[must_use]
    pub fn with_cover_ext(mut self, enabled: bool) -> Self {
        self.cover_ext = Some(enabled);
        self
    }

    /// Flow-cover separation. Default on.
    #[must_use]
    pub fn with_flowcover(mut self, enabled: bool) -> Self {
        self.flowcover = Some(enabled);
        self
    }

    /// Cut-coefficient snapping. Default on.
    #[must_use]
    pub fn with_snap(mut self, enabled: bool) -> Self {
        self.snap = Some(enabled);
        self
    }

    /// Set-partitioning LNS. Default on (auto-gated).
    #[must_use]
    pub fn with_splns(mut self, enabled: bool) -> Self {
        self.splns = Some(enabled);
        self
    }

    /// Market-share walk. Default on (auto-gated).
    #[must_use]
    pub fn with_ms_walk(mut self, enabled: bool) -> Self {
        self.ms_walk = Some(enabled);
        self
    }

    /// Sweep/prove wall split on routing models. Default on.
    #[must_use]
    pub fn with_sweep_prove(mut self, enabled: bool) -> Self {
        self.sweep_prove = Some(enabled);
        self
    }

    /// RINS cadence rescue. Default on.
    #[must_use]
    pub fn with_rins_rescue(mut self, enabled: bool) -> Self {
        self.rins_rescue = Some(enabled);
        self
    }

    /// MILP symmetry handling. Default on.
    #[must_use]
    pub fn with_sym(mut self, enabled: bool) -> Self {
        self.sym = Some(enabled);
        self
    }

    /// Pin best-bound node selection for all sub-MIP arms (default: DFS
    /// below level 3).
    #[must_use]
    pub fn with_submip_best_bound(mut self, enabled: bool) -> Self {
        self.submip_best_bound = Some(enabled);
        self
    }

    /// Force zero-half separation on beyond the pure-set-partitioning
    /// auto-arm.
    #[must_use]
    pub fn with_zero_half(mut self, enabled: bool) -> Self {
        self.zero_half = Some(enabled);
        self
    }

    /// Flip-LNS reach instrumentation (trace-only diagnostic). Default off.
    #[must_use]
    pub fn with_flip_reach(mut self, enabled: bool) -> Self {
        self.flip_reach = Some(enabled);
        self
    }

    /// Bound-propagation sweep cap.
    #[must_use]
    pub fn with_prop_sweeps(mut self, sweeps: usize) -> Self {
        self.prop_sweeps = Some(sweeps);
        self
    }

    /// Bound-propagation queue cap.
    #[must_use]
    pub fn with_prop_queue(mut self, queue: usize) -> Self {
        self.prop_queue = Some(queue);
        self
    }

    /// Set-partitioning LNS exposed-region cap.
    #[must_use]
    pub fn with_splns_exposed(mut self, cap: usize) -> Self {
        self.splns_exposed = Some(cap);
        self
    }

    /// Set-partitioning LNS node budget.
    #[must_use]
    pub fn with_splns_budget(mut self, nodes: usize) -> Self {
        self.splns_budget = Some(nodes);
        self
    }

    /// Set-partitioning LNS stall window, in seconds.
    ///
    /// # Errors
    ///
    /// [`EngineConfigError`] unless `secs` is finite and non-negative.
    pub fn with_splns_stall_secs(mut self, secs: f64) -> Result<Self, EngineConfigError> {
        self.splns_stall_secs = Some(checked(Knob::SplnsStall, secs, 0.0, f64::MAX)?);
        Ok(self)
    }

    /// Market-share walk move budget.
    #[must_use]
    pub fn with_ms_walk_moves(mut self, moves: usize) -> Self {
        self.ms_walk_moves = Some(moves);
        self
    }

    /// Print the frontier peek bound every N nodes (measurement).
    #[must_use]
    pub fn with_gub_meas_every(mut self, nodes: usize) -> Self {
        self.gub_meas_every = Some(nodes);
        self
    }

    /// Deterministic hashed cost perturbation magnitude (diagnostic).
    ///
    /// # Errors
    ///
    /// [`EngineConfigError`] unless `eps` is finite and non-negative.
    pub fn with_diag_cost_perturb(mut self, eps: f64) -> Result<Self, EngineConfigError> {
        self.diag_cost_perturb = Some(checked(Knob::DiagCostPerturb, eps, 0.0, f64::MAX)?);
        Ok(self)
    }

    /// Flow-cost branching mode: `0..=3`.
    ///
    /// # Errors
    ///
    /// [`EngineConfigError`] unless `mode <= 3`.
    pub fn with_fc_mode(mut self, mode: usize) -> Result<Self, EngineConfigError> {
        if mode > 3 {
            return Err(EngineConfigError::OutOfRange {
                knob: Knob::FcMode.label(),
                value: mode as f64,
                low: 0.0,
                high: 3.0,
            });
        }
        self.fc_mode = Some(mode);
        Ok(self)
    }

    /// Which arm solves the dual long-step's flip aggregate. Default
    /// [`crate::FlipSolveMode::Auto`].
    #[must_use]
    pub fn with_flip_solve(mut self, mode: crate::FlipSolveMode) -> Self {
        self.flip_solve = Some(mode);
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn b13_switches_reach_the_profile_with_the_single_inversion() {
        use crate::tune::Knob;
        // B13 spot checks: one of each carrier shape in the bab layer, plus
        // the one dual-role builder (odd-cycle force vs disable are distinct
        // knobs behind one positive-sense builder).
        let engine = EngineEconomics::default()
            .with_clique(false)
            .with_odd_cycle(true)
            .with_submip_best_bound(true)
            .with_prop_sweeps(11)
            .with_splns_stall_secs(2.5)
            .expect("finite non-negative stall")
            .with_fc_mode(2)
            .expect("mode 2 in domain");
        let _active = crate::tune::activate_caller(engine.profile());
        assert!(crate::tune::on(Knob::NoClique));
        assert!(crate::tune::on(Knob::OddCycle));
        assert!(!crate::tune::on(Knob::NoOddCycle));
        assert!(crate::tune::on(Knob::SubmipBb));
        assert_eq!(crate::tune::count(Knob::PropSweeps, 3), 11);
        assert_eq!(crate::tune::real_opt(Knob::SplnsStall), Some(2.5));
        assert_eq!(crate::tune::count_opt(Knob::FcMode), Some(2));
        assert!(EngineEconomics::default().with_fc_mode(4).is_err());
        assert!(
            EngineEconomics::default()
                .with_odd_cycle(false)
                .profile()
                .is_empty()
                == false
        );
        // And the env layer is not a party to these knobs at all.
        for knob in [Knob::NoClique, Knob::FcMode] {
            assert_eq!(knob.env(), None, "{knob:?} must have no env spelling");
        }
    }
}
