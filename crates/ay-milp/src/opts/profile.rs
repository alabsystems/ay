// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lowering from public engine settings to the internal knob profile.

use crate::tune::{Knob, Profile, Setting};

use super::EngineEconomics;

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
        self.extend_dual_simplex_profile(profile)
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
        if let Some(v) = self.gub_branch {
            p = p.with(Knob::NoGubBranch, Setting::Flag(!v));
        }
        if let Some(v) = self.dedup_cols {
            p = p.with(Knob::NoDedupCols, Setting::Flag(!v));
        }
        if let Some(v) = self.binary_complement_sub {
            p = p.with(Knob::NoBinaryComplementSub, Setting::Flag(!v));
        }
        if let Some(v) = self.lb_activity {
            p = p.with(Knob::NoLbAct, Setting::Flag(!v));
        }
        if let Some(v) = self.gi_dfs {
            p = p.with(Knob::NoGiDfs, Setting::Flag(!v));
        }
        if let Some(v) = self.impl_cut {
            p = p.with(Knob::NoImplCut, Setting::Flag(!v));
        }
        if let Some(v) = self.impl_tab {
            p = p.with(Knob::NoImplTab, Setting::Flag(!v));
        }
        if let Some(v) = self.knap_redirect {
            p = p.with(Knob::NoKnapRedirect, Setting::Flag(!v));
        }
        if let Some(v) = self.dive_skip {
            p = p.with(Knob::NoDiveSkip, Setting::Flag(!v));
        }
        if let Some(v) = self.cut_fma {
            p = p.with(Knob::NoCutFma, Setting::Flag(!v));
        }
        if let Some(v) = self.odd_lift {
            p = p.with(Knob::NoOddLift, Setting::Flag(!v));
        }
        if let Some(v) = self.strongcg {
            p = p.with(Knob::NoStrongcg, Setting::Flag(!v));
        }
        if let Some(v) = self.dense_gmi_lu {
            p = p.with(Knob::DenseGmiLu, Setting::Flag(v));
        }
        if let Some(v) = self.mir_knap {
            p = p.with(Knob::NoMirKnap, Setting::Flag(!v));
        }
        if let Some(v) = self.bound_branch {
            p = p.with(Knob::BbGate, Setting::Flag(v));
        }
        if let Some(v) = self.child_order {
            p = p.with(Knob::ChildOrderMode, Setting::Count(v));
        }
        if let Some(v) = self.cuts_per_round {
            p = p.with(Knob::CutsPerRound, Setting::Count(v));
        }
        if let Some(v) = self.cut_eff_floor {
            p = p.with(Knob::CutEffFloor, Setting::Real(v));
        }
        if let Some(v) = self.ft_spike {
            p = p.with(Knob::FtSpikeArm, Setting::Count(v));
        }
        if let Some(v) = self.gub_sb {
            p = p.with(Knob::GubSb, Setting::Flag(v));
        }
        if let Some(v) = self.ng_box {
            p = p.with(Knob::NgBox, Setting::Flag(v));
        }
        if let Some(v) = self.ng_branch_pct {
            p = p.with(Knob::NgBranchPct, Setting::Real(v));
        }
        if let Some(v) = self.node_prop {
            p = p.with(Knob::NodeProp, Setting::Flag(v));
        }
        if let Some(v) = self.sb_sustain {
            p = p.with(Knob::SbSustain, Setting::Flag(v));
        }
        if let Some(v) = self.plunge {
            p = p.with(Knob::Plunge, Setting::Flag(v));
        }
        if let Some(v) = self.gmi_rounds {
            p = p.with(Knob::GmiRounds, Setting::Count(v));
        }
        if let Some(v) = self.root_cuts_per_round {
            p = p.with(Knob::RootCutsPerRound, Setting::Count(v));
        }
        if let Some(v) = self.root_probe {
            p = p.with(Knob::RootProbe, Setting::Flag(v));
        }
        if let Some(v) = self.dfs {
            p = p.with(Knob::Dfs, Setting::Flag(v));
        }
        if let Some(v) = self.node_cuts {
            p = p.with(Knob::NodeCuts, Setting::Flag(v));
        }
        if let Some(v) = self.sym_branch_band {
            p = p.with(Knob::SymBranchBand, Setting::Real(v));
        }
        if let Some(v) = self.rins {
            p = p.with(Knob::Rins, Setting::Count(v));
        }
        if let Some(v) = self.dualfix_all {
            p = p.with(Knob::DualfixAll, Setting::Flag(v));
        }
        if let Some(v) = self.implied_bound {
            p = p.with(Knob::ImpliedBound, Setting::Flag(v));
        }
        if let Some(v) = self.lifted_cover {
            p = p.with(Knob::LiftedCover, Setting::Flag(v));
        }
        if let Some(v) = self.lnp_budget {
            p = p.with(Knob::LnpBudget, Setting::Count(v));
        }
        if let Some(v) = self.lattice_bkz_beta {
            p = p.with(Knob::LatticeBkzBeta, Setting::Count(v));
        }
        if let Some(v) = self.dual_perturb {
            p = p.with(Knob::DualPerturb, Setting::Real(v));
        }
        if let Some(v) = self.cert_grace_secs {
            p = p.with(Knob::CertGraceSecs, Setting::Real(v));
        }
        if let Some(v) = self.anchor_first_refusal_ms {
            p = p.with(Knob::AnchorFirstRefusalMs, Setting::Count(v));
        }
        if let Some(v) = self.rins_every {
            p = p.with(Knob::RinsEvery, Setting::Count(v));
        }
        if let Some(v) = self.rins_drycap {
            p = p.with(Knob::RinsDrycap, Setting::Count(v));
        }
        if let Some(v) = self.pump_share {
            p = p.with(Knob::PumpShare, Setting::Real(v));
        }
        if let Some(v) = self.setpart_share {
            p = p.with(Knob::SetpartShare, Setting::Real(v));
        }
        if let Some(v) = self.parity {
            p = p.with(Knob::NoParity, Setting::Flag(!v));
        }
        if let Some(v) = self.margin_reframe {
            p = p.with(Knob::NoMarginReframe, Setting::Flag(!v));
        }
        if let Some(v) = self.sym_mode {
            p = p.with(Knob::SymMode, Setting::Count(v));
        }
        if let Some(v) = self.heur_share {
            p = p.with(Knob::HeurShare, Setting::Real(v));
        }
        if let Some(v) = self.sb_rel {
            p = p.with(Knob::SbRel, Setting::Count(v));
        }
        if let Some(v) = self.sb_cands {
            p = p.with(Knob::SbCands, Setting::Count(v));
        }
        if let Some(v) = self.sb_total {
            p = p.with(Knob::SbTotal, Setting::Count(v));
        }
        if let Some(v) = self.presolve {
            p = p.with(Knob::NoPresolve, Setting::Flag(!v));
        }
        if let Some(v) = self.presolve_scout {
            p = p.with(Knob::NoPresolveScout, Setting::Flag(!v));
        }
        if let Some(v) = self.vsids {
            p = p.with(Knob::Vsids, Setting::Flag(v));
        }
        if let Some(v) = self.root_probe_all {
            p = p.with(Knob::RootProbeAll, Setting::Flag(v));
        }
        if let Some(v) = self.sepstat {
            p = p.with(Knob::Sepstat, Setting::Flag(v));
        }
        if let Some(v) = self.lp_stats {
            p = p.with(Knob::LpStats, Setting::Flag(v));
        }
        if let Some(v) = self.step_trace {
            p = p.with(Knob::StepTraceN, Setting::Count(v));
        }
        if let Some(v) = self.bump_diag {
            p = p.with(Knob::BumpDiag, Setting::Flag(v));
        }
        if let Some(v) = self.bumpdiff_lanes {
            p = p.with(Knob::BumpdiffLanes, Setting::Count(v));
        }
        if let Some(v) = self.diag_plain_cold {
            p = p.with(Knob::DiagPlainCold, Setting::Flag(v));
        }
        if let Some(v) = self.dump_vertex {
            p = p.with(Knob::DumpVertex, Setting::Flag(v));
        }
        if let Some(v) = self.smt_lane {
            p = p.with(Knob::SmtLane, Setting::Flag(v));
        }
        if let Some(v) = self.max_nodes {
            p = p.with(Knob::MaxNodes, Setting::Count(v));
        }
        if let Some(v) = self.struct_elim {
            p = p.with(Knob::StructElim, Setting::Flag(v));
        }
        if let Some(v) = self.bound_cover {
            p = p.with(Knob::NoBoundCover, Setting::Flag(!v));
        }
        if let Some(v) = self.pump_iter_mult {
            p = p.with(Knob::PumpIterMult, Setting::Real(v));
        }
        if let Some(v) = self.pump_iter_cap {
            p = p.with(Knob::NoPumpIterCap, Setting::Flag(!v));
        }
        if let Some(v) = self.ng_up {
            p = p.with(Knob::NgUp, Setting::Flag(v));
        }
        if let Some(v) = self.cut_shadow {
            p = p.with(Knob::CutShadow, Setting::Count(v as usize));
        }
        if let Some(v) = self.chain_agg {
            p = p.with(Knob::ChainAgg, Setting::Flag(v));
        }
        if let Some(v) = self.auto_margin {
            p = p.with(Knob::AutoMargin, Setting::Flag(v));
        }
        if let Some(v) = self.impl_lane {
            p = p.with(Knob::ImplLane, Setting::Flag(v));
        }
        if let Some(v) = self.impl_arm {
            p = p.with(Knob::ImplArm, Setting::Count(v));
        }
        if let Some(v) = self.prop_conflict {
            p = p.with(Knob::PropConflict, Setting::Flag(v));
        }
        if let Some(v) = self.lb_conflict {
            p = p.with(Knob::LbConflict, Setting::Count(v as usize));
        }
        if let Some(v) = self.lb_arm {
            p = p.with(Knob::LbArm, Setting::Count(v));
        }
        if let Some(v) = self.lb_strict {
            p = p.with(Knob::LbStrict, Setting::Flag(v));
        }
        if let Some(v) = self.dual_cutoff {
            p = p.with(Knob::DualCutoff, Setting::Real(v));
        }
        p
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
