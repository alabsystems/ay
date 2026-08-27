// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lowering from public engine settings to the internal knob profile.

use crate::tune::{Knob, Profile, Setting};

use super::EngineEconomics;

mod affine;

fn inverted_flag(enabled: bool) -> Setting {
    Setting::Flag(!enabled)
}

fn count<T: Into<usize>>(value: T) -> Setting {
    Setting::Count(value.into())
}

/// Apply one ordered batch in a narrow loop.
///
/// [`Profile::with`] consumes its large array carrier. Centralizing that move
/// here prevents straight-line lowering from reserving a separate stack
/// temporary for every setting in a batch.
fn extend_with_settings<const N: usize>(
    profile: &mut Profile,
    settings: [(Knob, Option<Setting>); N],
) {
    for (knob, value) in settings {
        if let Some(value) = value {
            *profile = (*profile).with(knob, value);
        }
    }
}

impl EngineEconomics {
    /// Lower these settings into the engine's internal knob carrier.
    ///
    /// The `No*` inversions happen here and only here: the public surface is
    /// positive-sense (`with_cuts(false)`) because that is what reads correctly
    /// at a call site, while the knob keeps the environment's own spelling
    /// because an operator's `--no-cuts` has to keep meaning what it
    /// has always meant.
    pub(crate) fn profile(&self) -> Profile {
        let profile = self.base_profile();
        let profile = self.extend_retired_env_profile(profile);
        let profile = self.extend_branch_and_bound_profile(profile);
        let profile = self.extend_dual_simplex_profile(profile);
        self.extend_census_profile(profile)
    }

    fn base_profile(&self) -> Profile {
        let mut p = Profile::EMPTY;
        if let Some(v) = self.lattice {
            p = p.with(Knob::NoLattice, Setting::Flag(!v));
        }
        if let Some(v) = self.saturation_stop {
            p = p.with(Knob::NoSatStop, Setting::Flag(!v));
        }
        if let Some(v) = self.saturation_stop_floor {
            p = p.with(Knob::SatStopSecs, Setting::Real(v));
        }
        if let Some(v) = self.saturation_stop_multiplier {
            p = p.with(Knob::SatStopMult, Setting::Real(v));
        }
        if let Some(v) = self.bloom_cap_relaxation {
            p = p.with(Knob::NoBloomRelax, Setting::Flag(!v));
        }
        if let Some(v) = self.flip_lns_cap {
            p = p.with(Knob::FlipCapSecs, Setting::Real(v));
        }
        if let Some(v) = self.flip_lns_share {
            p = p.with(Knob::FlipShare, Setting::Real(v));
        }
        if let Some(v) = self.warm_lu {
            p = p.with(Knob::WarmLu, Setting::Flag(v));
        }
        if let Some(v) = self.presolve_share {
            p = p.with(Knob::PresolveShare, Setting::Real(v));
        }
        if let Some(v) = self.cuts {
            p = p.with(Knob::NoCuts, Setting::Flag(!v));
        }
        if let Some(v) = self.pump_restarts {
            p = p.with(Knob::PumpRestarts, Setting::Count(v));
        }
        if let Some(v) = self.dive_max_pins {
            p = p.with(Knob::DiveMaxPins, Setting::Count(v));
        }
        if let Some(v) = self.dual_fixing {
            p = p.with(Knob::NoDualfix, Setting::Flag(!v));
        }
        if let Some(v) = self.kernel_reformulation {
            p = p.with(Knob::NoKernelReform, Setting::Flag(!v));
        }
        if let Some(v) = self.certificate_decoupling {
            p = p.with(Knob::NoCertDecouple, Setting::Flag(!v));
        }
        if let Some(v) = self.feasibility_conflict {
            p = p.with(Knob::NoFeasConflict, Setting::Flag(!v));
        }
        if let Some(v) = self.cold_root_lu {
            p = p.with(Knob::NoColdLu, Setting::Flag(!v));
        }
        if let Some(v) = self.vub {
            p = p.with(Knob::NoVub, Setting::Flag(!v));
        }
        if let Some(v) = self.mir_genint {
            p = p.with(Knob::NoMirGenint, Setting::Flag(!v));
        }
        if let Some(v) = self.sep_screen {
            p = p.with(Knob::NoSepScreen, Setting::Flag(!v));
        }
        if let Some(v) = self.ft_fast {
            p = p.with(Knob::NoFtFast, Setting::Flag(!v));
        }
        if let Some(v) = self.ftran_fast {
            p = p.with(Knob::NoFtranFast, Setting::Flag(!v));
        }
        if let Some(v) = self.ftran_nz_fast {
            p = p.with(Knob::NoFtranNzFast, Setting::Flag(!v));
        }
        if let Some(v) = self.countsort {
            p = p.with(Knob::NoCountsort, Setting::Flag(!v));
        }
        if let Some(v) = self.coef_tighten {
            p = p.with(Knob::NoCoefTighten, Setting::Flag(!v));
        }
        if let Some(v) = self.orbitope {
            p = p.with(Knob::NoOrbitope, Setting::Flag(!v));
        }
        if let Some(v) = self.ft_growth_tol {
            p = p.with(Knob::FtGrowthTol, Setting::Real(v));
        }
        p
    }

    fn extend_retired_env_profile(&self, mut p: Profile) -> Profile {
        self.extend_retired_feature_profile(&mut p);
        self.extend_retired_search_profile(&mut p);
        self.extend_retired_presolve_and_diagnostics_profile(&mut p);
        p = affine::extend_reduction_profile(self, p);
        self.extend_retired_post_reduction_profile(&mut p);
        p
    }

    fn extend_retired_feature_profile(&self, profile: &mut Profile) {
        extend_with_settings(
            profile,
            [
                (Knob::NoGubBranch, self.gub_branch.map(inverted_flag)),
                (Knob::NoDedupCols, self.dedup_cols.map(inverted_flag)),
                (
                    Knob::NoBinaryComplementSub,
                    self.binary_complement_sub.map(inverted_flag),
                ),
                (Knob::NoLbAct, self.lb_activity.map(inverted_flag)),
                (Knob::NoGiDfs, self.gi_dfs.map(inverted_flag)),
                (Knob::NoImplCut, self.impl_cut.map(inverted_flag)),
                (Knob::NoImplTab, self.impl_tab.map(inverted_flag)),
                (Knob::NoKnapRedirect, self.knap_redirect.map(inverted_flag)),
                (Knob::NoDiveSkip, self.dive_skip.map(inverted_flag)),
                (Knob::NoCutFma, self.cut_fma.map(inverted_flag)),
                (Knob::NoOddLift, self.odd_lift.map(inverted_flag)),
                (Knob::NoStrongcg, self.strongcg.map(inverted_flag)),
                (Knob::DenseGmiLu, self.dense_gmi_lu.map(Setting::Flag)),
                (Knob::NoMirKnap, self.mir_knap.map(inverted_flag)),
            ],
        )
    }

    fn extend_retired_search_profile(&self, profile: &mut Profile) {
        extend_with_settings(
            profile,
            [
                (Knob::BbGate, self.bound_branch.map(Setting::Flag)),
                (Knob::ChildOrderMode, self.child_order.map(count)),
                (Knob::CutsPerRound, self.cuts_per_round.map(count)),
                (Knob::CutEffFloor, self.cut_eff_floor.map(Setting::Real)),
                (Knob::FtSpikeArm, self.ft_spike.map(count)),
                (Knob::GubSb, self.gub_sb.map(Setting::Flag)),
                (Knob::NgBox, self.ng_box.map(Setting::Flag)),
                (Knob::NgBranchPct, self.ng_branch_pct.map(Setting::Real)),
                (Knob::NodeProp, self.node_prop.map(Setting::Flag)),
                (Knob::SbSustain, self.sb_sustain.map(Setting::Flag)),
                (Knob::Plunge, self.plunge.map(Setting::Flag)),
                (Knob::GmiRounds, self.gmi_rounds.map(count)),
                (Knob::RootCutsPerRound, self.root_cuts_per_round.map(count)),
                (Knob::RootProbe, self.root_probe.map(Setting::Flag)),
                (Knob::Dfs, self.dfs.map(Setting::Flag)),
                (Knob::NodeCuts, self.node_cuts.map(Setting::Flag)),
                (Knob::SymBranchBand, self.sym_branch_band.map(Setting::Real)),
                (Knob::Rins, self.rins.map(count)),
                (Knob::DualfixAll, self.dualfix_all.map(Setting::Flag)),
                (Knob::ImpliedBound, self.implied_bound.map(Setting::Flag)),
                (Knob::LiftedCover, self.lifted_cover.map(Setting::Flag)),
                (Knob::LnpBudget, self.lnp_budget.map(count)),
                (Knob::LatticeBkzBeta, self.lattice_bkz_beta.map(count)),
                (Knob::DualPerturb, self.dual_perturb.map(Setting::Real)),
                (Knob::CertGraceSecs, self.cert_grace_secs.map(Setting::Real)),
                (
                    Knob::AnchorFirstRefusalMs,
                    self.anchor_first_refusal_ms.map(count),
                ),
                (Knob::RinsEvery, self.rins_every.map(count)),
                (Knob::RinsDrycap, self.rins_drycap.map(count)),
                (Knob::PumpShare, self.pump_share.map(Setting::Real)),
                (Knob::SetpartShare, self.setpart_share.map(Setting::Real)),
                (Knob::NoParity, self.parity.map(inverted_flag)),
                (
                    Knob::NoMarginReframe,
                    self.margin_reframe.map(inverted_flag),
                ),
                (Knob::SymMode, self.sym_mode.map(count)),
                (Knob::HeurShare, self.heur_share.map(Setting::Real)),
                (Knob::SbRel, self.sb_rel.map(count)),
                (Knob::SbCands, self.sb_cands.map(count)),
                (Knob::SbTotal, self.sb_total.map(count)),
            ],
        )
    }

    fn extend_retired_presolve_and_diagnostics_profile(&self, profile: &mut Profile) {
        extend_with_settings(
            profile,
            [
                (Knob::NoPresolve, self.presolve.map(inverted_flag)),
                (
                    Knob::NoPresolveScout,
                    self.presolve_scout.map(inverted_flag),
                ),
                (Knob::Vsids, self.vsids.map(Setting::Flag)),
                (Knob::RootProbeAll, self.root_probe_all.map(Setting::Flag)),
                (Knob::Sepstat, self.sepstat.map(Setting::Flag)),
                (
                    Knob::RootClosurePresolve,
                    self.root_closure_presolve.map(Setting::Flag),
                ),
                (Knob::TableauMir, self.tableau_mir.map(Setting::Flag)),
                (Knob::MirAggRoot, self.mir_agg_root.map(Setting::Flag)),
                (Knob::LpStats, self.lp_stats.map(Setting::Flag)),
                (Knob::StepTraceN, self.step_trace.map(count)),
                (Knob::BumpDiag, self.bump_diag.map(Setting::Flag)),
                (Knob::BumpdiffLanes, self.bumpdiff_lanes.map(count)),
                (Knob::DiagPlainCold, self.diag_plain_cold.map(Setting::Flag)),
                (Knob::DumpVertex, self.dump_vertex.map(Setting::Flag)),
                (Knob::SmtLane, self.smt_lane.map(Setting::Flag)),
                (Knob::MaxNodes, self.max_nodes.map(count)),
            ],
        )
    }

    fn extend_retired_post_reduction_profile(&self, profile: &mut Profile) {
        extend_with_settings(
            profile,
            [
                (Knob::NoBoundCover, self.bound_cover.map(inverted_flag)),
                (Knob::PumpIterMult, self.pump_iter_mult.map(Setting::Real)),
                (Knob::NoPumpIterCap, self.pump_iter_cap.map(inverted_flag)),
                (Knob::NgUp, self.ng_up.map(Setting::Flag)),
                (Knob::CutShadow, self.cut_shadow.map(count)),
                (Knob::ChainAgg, self.chain_agg.map(Setting::Flag)),
                (Knob::AutoMargin, self.auto_margin.map(Setting::Flag)),
                (Knob::ImplLane, self.impl_lane.map(Setting::Flag)),
                (Knob::ImplArm, self.impl_arm.map(count)),
                (Knob::DroughtDive, self.drought_dive.map(count)),
                (Knob::PropConflict, self.prop_conflict.map(Setting::Flag)),
                (Knob::LbConflict, self.lb_conflict.map(count)),
                (Knob::LbArm, self.lb_arm.map(count)),
                (Knob::LbStrict, self.lb_strict.map(Setting::Flag)),
                (Knob::DualCutoff, self.dual_cutoff.map(Setting::Real)),
            ],
        )
    }

    fn extend_branch_and_bound_profile(&self, mut p: Profile) -> Profile {
        if let Some(v) = self.flowcover_agg {
            p = p.with(Knob::NoFlowcoverAgg, Setting::Flag(!v));
        }
        if let Some(v) = self.gi_ext {
            p = p.with(Knob::NoGiExt, Setting::Flag(!v));
        }
        if let Some(v) = self.bottleneck_ext {
            p = p.with(Knob::NoBottleneckExt, Setting::Flag(!v));
        }
        if let Some(v) = self.clique {
            p = p.with(Knob::NoClique, Setting::Flag(!v));
        }
        if let Some(v) = self.odd_cycle_off {
            p = p.with(Knob::NoOddCycle, Setting::Flag(v));
        }
        if let Some(v) = self.cover_ext {
            p = p.with(Knob::NoCoverExt, Setting::Flag(!v));
        }
        if let Some(v) = self.flowcover {
            p = p.with(Knob::NoFlowcover, Setting::Flag(!v));
        }
        if let Some(v) = self.snap {
            p = p.with(Knob::NoSnap, Setting::Flag(!v));
        }
        if let Some(v) = self.splns {
            p = p.with(Knob::NoSplns, Setting::Flag(!v));
        }
        if let Some(v) = self.ms_walk {
            p = p.with(Knob::NoMsWalk, Setting::Flag(!v));
        }
        if let Some(v) = self.sweep_prove {
            p = p.with(Knob::NoSweepProve, Setting::Flag(!v));
        }
        if let Some(v) = self.rins_rescue {
            p = p.with(Knob::NoRinsRescue, Setting::Flag(!v));
        }
        if let Some(v) = self.sym {
            p = p.with(Knob::NoSym, Setting::Flag(!v));
        }
        if let Some(v) = self.submip_best_bound {
            p = p.with(Knob::SubmipBb, Setting::Flag(v));
        }
        if let Some(v) = self.zero_half {
            p = p.with(Knob::ZeroHalf, Setting::Flag(v));
        }
        if let Some(v) = self.odd_cycle_on {
            p = p.with(Knob::OddCycle, Setting::Flag(v));
        }
        if let Some(v) = self.flip_reach {
            p = p.with(Knob::FlipReach, Setting::Flag(v));
        }
        if let Some(v) = self.prop_sweeps {
            p = p.with(Knob::PropSweeps, Setting::Count(v));
        }
        if let Some(v) = self.prop_queue {
            p = p.with(Knob::PropQueue, Setting::Count(v));
        }
        if let Some(v) = self.splns_exposed {
            p = p.with(Knob::SplnsExposed, Setting::Count(v));
        }
        if let Some(v) = self.splns_budget {
            p = p.with(Knob::SplnsBudget, Setting::Count(v));
        }
        if let Some(v) = self.splns_stall_secs {
            p = p.with(Knob::SplnsStall, Setting::Real(v));
        }
        if let Some(v) = self.ms_walk_moves {
            p = p.with(Knob::MsWalkMoves, Setting::Count(v));
        }
        if let Some(v) = self.gub_meas_every {
            p = p.with(Knob::GubMeasEvery, Setting::Count(v));
        }
        if let Some(v) = self.diag_cost_perturb {
            p = p.with(Knob::DiagCostPerturb, Setting::Real(v));
        }
        if let Some(v) = self.fc_mode {
            p = p.with(Knob::FcMode, Setting::Count(v));
        }
        if let Some(v) = self.flip_solve {
            let mode = match v {
                crate::FlipSolveMode::Auto => 0,
                crate::FlipSolveMode::Sparse => 1,
                crate::FlipSolveMode::Dense => 2,
            };
            p = p.with(Knob::FlipSolve, Setting::Count(mode));
        }
        p
    }
}
