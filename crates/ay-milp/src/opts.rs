// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solve options.

use crate::tune::Knob;
use std::time::{Duration, Instant};

mod branch_and_bound;
mod carriers;
mod config;
mod dual_simplex;
mod profile;

pub use config::EngineConfigError;
use config::{checked, MAX_KNOB_SECS};
pub use dual_simplex::TallColdDualMode;

/// Per-solve engine search economics.
/// # What this is for
///
/// Every knob here was reachable only through a process-global `AY_MILP_*`
/// environment variable. That is not merely inelegant for an in-process
/// consumer: `std::env::set_var` races with a concurrent `getenv` (hence
/// `unsafe` in edition 2024), and ay-milp's primary consumer is a
/// multi-threaded verifier whose workers can be inside one solve while another
/// thread configures the next. It also makes per-instance policy impossible —
/// a recipe for one model class necessarily applies to every concurrent solve
/// in the process. the development design notes §M1 is the
/// full statement of the problem.
///
/// These settings are **per-`SolveOpts`**, carried on the solve rather than on
/// the process, so two concurrent sessions can differ. They also outrank the
/// environment, so a stray `AY_MILP_*` inherited from a CI shell cannot
/// reconfigure a solve that set them.
///
/// # Every field is optional, and that is load-bearing
///
/// `None` means *this solve has no opinion*, and resolution falls through to
/// exactly the environment variable and compiled default the engine used
/// before. A default `EngineEconomics` is therefore bit-identical in behaviour
/// to not having one, which is what makes it safe to put on every
/// [`SolveOpts`].
///
/// # Soundness class
///
/// These settings steer search without bypassing session point, value, or
/// certificate checks. They can change which incumbent or bound is reached and
/// whether a tree closes inside the budget. Some claims — notably integral
/// optimality, uncertified infeasibility, unboundedness, and standalone bounds —
/// are not complete exported proofs. [`crate::Outcome::evidence_shape`] only
/// reports required fields; [`crate::Outcome::check_against`] validates those
/// fields and refuses search-only claims.
///
/// [`with_lattice`](Self::with_lattice) can return `Optimal { cert: None }`.
/// Requiring certificates rejects defined shapes missing their artifact; it
/// neither proves an artifact nor closes an integral branch-and-bound tree.
#[derive(Debug, Clone, Copy, PartialEq, Default)]
#[non_exhaustive]
pub struct EngineEconomics {
    lattice: Option<bool>,
    saturation_stop: Option<bool>,
    saturation_stop_floor: Option<f64>,
    saturation_stop_multiplier: Option<f64>,
    bloom_cap_relaxation: Option<bool>,
    flip_lns_cap: Option<f64>,
    flip_lns_share: Option<f64>,
    warm_lu: Option<bool>,
    presolve_share: Option<f64>,
    cuts: Option<bool>,
    pump_restarts: Option<usize>,
    dive_max_pins: Option<usize>,
    dual_fixing: Option<bool>,
    kernel_reformulation: Option<bool>,
    certificate_decoupling: Option<bool>,
    feasibility_conflict: Option<bool>,
    cold_root_lu: Option<bool>,
    vub: Option<bool>,
    mir_genint: Option<bool>,
    sep_screen: Option<bool>,
    ft_fast: Option<bool>,
    ftran_fast: Option<bool>,
    ftran_nz_fast: Option<bool>,
    countsort: Option<bool>,
    coef_tighten: Option<bool>,
    orbitope: Option<bool>,
    ft_growth_tol: Option<f64>,
    dual_anatomy: Option<bool>,
    verify_after: Option<usize>,
    fused_rt: Option<bool>,
    rt_kind: Option<bool>,
    iter_profile: Option<bool>,
    rt_bits_key: Option<bool>,
    wide_bloom: Option<bool>,
    eta_reuse: Option<bool>,
    devex: Option<bool>,
    cold_dual: Option<bool>,
    tri_crash: Option<bool>,
    chain_devex: Option<usize>,
    cutoff_stop: Option<bool>,
    node_lu: Option<bool>,
    tall_lu: Option<bool>,
    tall_cold_dual: Option<bool>,
    dual_churn_band: Option<bool>,
    dual_bloom_cap: Option<usize>,
    flowcover_agg: Option<bool>,
    gi_ext: Option<bool>,
    bottleneck_ext: Option<bool>,
    clique: Option<bool>,
    odd_cycle_off: Option<bool>,
    cover_ext: Option<bool>,
    flowcover: Option<bool>,
    snap: Option<bool>,
    splns: Option<bool>,
    ms_walk: Option<bool>,
    sweep_prove: Option<bool>,
    rins_rescue: Option<bool>,
    sym: Option<bool>,
    submip_best_bound: Option<bool>,
    zero_half: Option<bool>,
    odd_cycle_on: Option<bool>,
    flip_reach: Option<bool>,
    prop_sweeps: Option<usize>,
    prop_queue: Option<usize>,
    splns_exposed: Option<usize>,
    splns_budget: Option<usize>,
    splns_stall_secs: Option<f64>,
    ms_walk_moves: Option<usize>,
    gub_meas_every: Option<usize>,
    diag_cost_perturb: Option<f64>,
    fc_mode: Option<usize>,
    flip_solve: Option<FlipSolveMode>,
    gub_branch: Option<bool>,
    dedup_cols: Option<bool>,
    binary_complement_sub: Option<bool>,
    lb_activity: Option<bool>,
    gi_dfs: Option<bool>,
    impl_cut: Option<bool>,
    impl_tab: Option<bool>,
    knap_redirect: Option<bool>,
    dive_skip: Option<bool>,
    cut_fma: Option<bool>,
    odd_lift: Option<bool>,
    strongcg: Option<bool>,
    dense_gmi_lu: Option<bool>,
    chain_shape: Option<bool>,
    chain_preorder: Option<bool>,
    bump_lu: Option<bool>,
    dual_bypass: Option<usize>,
    eager_perturb: Option<usize>,
    harris_rt: Option<usize>,
    float_lane: Option<bool>,
    mir_knap: Option<bool>,
    bound_branch: Option<bool>,
    child_order: Option<usize>,
    cuts_per_round: Option<usize>,
    cut_eff_floor: Option<f64>,
    ft_spike: Option<usize>,
    gub_sb: Option<bool>,
    ng_box: Option<bool>,
    ng_branch_pct: Option<f64>,
    node_prop: Option<bool>,
    sb_sustain: Option<bool>,
    plunge: Option<bool>,
    gmi_rounds: Option<usize>,
    root_cuts_per_round: Option<usize>,
    root_probe: Option<bool>,
    dfs: Option<bool>,
    node_cuts: Option<bool>,
    sym_branch_band: Option<f64>,
    rins: Option<usize>,
    dualfix_all: Option<bool>,
    implied_bound: Option<bool>,
    lifted_cover: Option<bool>,
    lnp_budget: Option<usize>,
    lattice_bkz_beta: Option<usize>,
    dual_perturb: Option<f64>,
    cert_grace_secs: Option<f64>,
    anchor_first_refusal_ms: Option<usize>,
    rins_every: Option<usize>,
    rins_drycap: Option<usize>,
    pump_share: Option<f64>,
    setpart_share: Option<f64>,
    parity: Option<bool>,
    margin_reframe: Option<bool>,
    sym_mode: Option<usize>,
    heur_share: Option<f64>,
    sb_rel: Option<usize>,
    sb_cands: Option<usize>,
    sb_total: Option<usize>,
    presolve: Option<bool>,
    presolve_scout: Option<bool>,
    vsids: Option<bool>,
    root_probe_all: Option<bool>,
    sepstat: Option<bool>,
    root_closure_presolve: Option<bool>,
    tableau_mir: Option<bool>,
    mir_agg_root: Option<bool>,
    lp_stats: Option<bool>,
    step_trace: Option<usize>,
    bump_diag: Option<bool>,
    bumpdiff_lanes: Option<usize>,
    diag_plain_cold: Option<bool>,
    dump_vertex: Option<bool>,
    smt_lane: Option<bool>,
    max_nodes: Option<usize>,
    struct_elim: Option<bool>,
    affine_agg: Option<bool>,
    bound_cover: Option<bool>,
    pump_iter_mult: Option<f64>,
    pump_iter_cap: Option<bool>,
    ng_up: Option<bool>,
    cut_shadow: Option<u8>,
    chain_agg: Option<bool>,
    auto_margin: Option<bool>,
    impl_lane: Option<bool>,
    impl_arm: Option<usize>,
    drought_dive: Option<usize>,
    prop_conflict: Option<bool>,
    lb_conflict: Option<u8>,
    lb_arm: Option<usize>,
    lb_strict: Option<bool>,
    dual_cutoff: Option<f64>,
    // ------------------------------------------------------------------
    // CARRIERS FOR THE READER-WITHOUT-WRITER CENSUS (`opts/carriers.rs`).
    //
    // Each knob had a reader but no writer, making its CLI switch unrecognised and inert.
    // `tests/knob_census.rs` fails if that state returns. Every field remains
    // `None` by default, so no compiled default moves.
    // ------------------------------------------------------------------
    singleton_sub: Option<bool>,
    node_cut_eager: Option<bool>,
    amo_multiway: Option<bool>,
    node_rc: Option<bool>,
    rc_cap_guard: Option<bool>,
    tri_crash_all: Option<bool>,
    sym_branch: Option<bool>,
    stab_orbit: Option<bool>,
    orbitope_dyn: Option<bool>,
    tree_floor: Option<bool>,
    tree_bound_outcome: Option<bool>,
    root_floor: Option<bool>,
    cover_minimal: Option<bool>,
    gub_clique: Option<bool>,
    gmi_cut_trace: Option<bool>,
    cond_tighten: Option<bool>,
    mod_k: Option<bool>,
    knap_dbg: Option<bool>,
    cold_dual_all: Option<bool>,
    cut_warm: Option<bool>,
    rlt: Option<bool>,
    dive_commit_stopped: Option<bool>,
    root_warm: Option<bool>,
    orbitope_branch: Option<bool>,
    orbitope_ilv: Option<bool>,
    orbitope_branch_dyn: Option<bool>,
    node_cut_local: Option<bool>,
    cond_scout: Option<bool>,
    hybrid_pb_lp: Option<bool>,
    attrib: Option<bool>,
    acensus: Option<bool>,
    hybrid_term: Option<bool>,
    root_probe_lp_rank: Option<bool>,
    ms_dive: Option<bool>,
    mas74_plunge: Option<bool>,
    relax_lift: Option<bool>,
    force_devex: Option<bool>,
    bump_btf: Option<bool>,
    node_cut_slots: Option<usize>,
    node_cut_every: Option<usize>,
    node_gmi: Option<usize>,
    node_gmi_every: Option<usize>,
    scale: Option<usize>,
    cut_topk: Option<usize>,
    sb_probe_iters: Option<usize>,
    root_probe_cap: Option<usize>,
    root_probe_clique_cap: Option<usize>,
    node_cut_batch: Option<usize>,
    node_cut_age: Option<usize>,
    ms_dive_steps: Option<usize>,
    gmi_max_rows: Option<usize>,
    chain_probe: Option<usize>,
    bump_lu_min: Option<usize>,
    cold_lu_eta_rebuilds: Option<usize>,
    adopt_ft_max_rows: Option<usize>,
    refactor_every: Option<usize>,
    eta_cap_mult: Option<usize>,
    lu_max_fill_nnz: Option<usize>,
    node_gmi_margin: Option<f64>,
    dive_probe_secs: Option<f64>,
    rens_window: Option<f64>,
    root_probe_share: Option<f64>,
    prop_first: Option<f64>,
}

/// Which arm solves the dual long-step's flip aggregate (B19).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FlipSolveMode {
    /// Per-commit density test (the FT-spike predicted-marked-set rule),
    /// dense on ties. The default.
    Auto,
    /// Force the sparse Gilbert–Peierls arm (needs a live LU engine).
    Sparse,
    /// Force the dense sweep (the historical default arm).
    Dense,
}

impl EngineEconomics {
    /// No opinion about anything: behaviourally identical to the default
    /// engine.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Run the market-split lattice detector (`--no-lattice`).
    ///
    /// Default on. It is self-gating on the markshare1 shape and silent on
    /// every other model, but it can return `Optimal { cert: None }`, so a
    /// consumer that treats optimal values as rigorous bounds may prefer it
    /// off — or, better, may prefer
    /// [`SolveOpts::with_require_certificates`], which already maps that
    /// outcome to `Unknown { CertificateUnavailable }`.
    #[must_use]
    pub fn with_lattice(mut self, enabled: bool) -> Self {
        self.lattice = Some(enabled);
        self
    }

    /// Run the flip-LNS saturation stop (`--no-sat-stop`).
    ///
    /// Default on, scoped to `tall_lu` models. It hands a saturated incumbent
    /// walk's remaining budget to the tree.
    #[must_use]
    pub fn with_saturation_stop(mut self, enabled: bool) -> Self {
        self.saturation_stop = Some(enabled);
        self
    }

    /// Dry-spell floor before the flip-LNS walk counts as saturated
    /// (`--sat-stop-secs`; default 15 s).
    #[must_use]
    pub fn with_saturation_stop_floor(mut self, floor: Duration) -> Self {
        self.saturation_stop_floor = Some(floor.as_secs_f64().min(MAX_KNOB_SECS));
        self
    }

    /// Multiplier on the largest observed improvement gap, above which a dry
    /// spell counts as saturation (`--sat-stop-mult`; default 1.5).
    ///
    /// # Errors
    ///
    /// [`EngineConfigError`] if `multiplier` is not finite and non-negative;
    /// the value multiplies a `Duration`, which panics on either.
    pub fn with_saturation_stop_multiplier(
        mut self,
        multiplier: f64,
    ) -> Result<Self, EngineConfigError> {
        self.saturation_stop_multiplier =
            Some(checked(Knob::SatStopMult, multiplier, 0.0, MAX_KNOB_SECS)?);
        Ok(self)
    }

    /// Relax the bloom cap on tall-degenerate warm dual walks
    /// (`--no-bloom-relax`).
    ///
    /// Default on. Verdict-neutral either way: it changes only the float pivot
    /// sequence, and every exit is re-checked and every leaf re-derived
    /// exactly.
    #[must_use]
    pub fn with_bloom_cap_relaxation(mut self, enabled: bool) -> Self {
        self.bloom_cap_relaxation = Some(enabled);
        self
    }

    /// Absolute cap on the flip-LNS window for `tall_lu` models
    /// (`--flip-cap-secs`).
    ///
    /// Ignored when [`with_flip_lns_share`](Self::with_flip_lns_share) is also
    /// set, which opts into the pure fractional schedule — the same coupling
    /// the environment variables have always had.
    #[must_use]
    pub fn with_flip_lns_cap(mut self, cap: Duration) -> Self {
        self.flip_lns_cap = Some(cap.as_secs_f64().min(MAX_KNOB_SECS));
        self
    }

    /// Fraction of the remaining budget given to the flip-LNS incumbent walk
    /// (`--flip-share`).
    ///
    /// Setting this also **disables the absolute cap**, restoring the pure
    /// fractional schedule on both LP lanes.
    ///
    /// # Errors
    ///
    /// [`EngineConfigError`] unless `share` is finite and in `[0, 1]`. A share
    /// above 1 would ask for a window longer than the budget it is a share of.
    pub fn with_flip_lns_share(mut self, share: f64) -> Result<Self, EngineConfigError> {
        self.flip_lns_share = Some(checked(Knob::FlipShare, share, 0.0, 1.0)?);
        Ok(self)
    }

    /// Install an LU engine in the pooled bound-change re-solver
    /// (`--warm-lu`).
    ///
    /// Default **off**, and deliberately so: the LU inverse is not bitwise the
    /// eta inverse, so it can move which LP vertex the flip-LNS lands on and
    /// therefore which incumbent it rounds. Gated to `tall_lu`/`wide_tall`
    /// models either way.
    #[must_use]
    pub fn with_warm_lu(mut self, enabled: bool) -> Self {
        self.warm_lu = Some(enabled);
        self
    }

    /// Fraction of the remaining budget given to bound-propagation presolve
    /// (`--presolve-share`).
    ///
    /// A short presolve deadline yields weaker-but-valid partial bounds, never
    /// a wrong one: the cap trades bound tightness for tree budget and cannot
    /// trade correctness.
    ///
    /// # Errors
    ///
    /// [`EngineConfigError`] unless `share` is finite and in `[0, 1]`.
    pub fn with_presolve_share(mut self, share: f64) -> Result<Self, EngineConfigError> {
        self.presolve_share = Some(checked(Knob::PresolveShare, share, 0.0, 1.0)?);
        Ok(self)
    }

    /// Separate cuts at the root (`--no-cuts`).
    ///
    /// Default on.
    #[must_use]
    pub fn with_cuts(mut self, enabled: bool) -> Self {
        self.cuts = Some(enabled);
        self
    }

    /// Extract variable upper bounds for cut separation. Default on.
    /// (B11: carried here; the never-set `AY_MILP_NO_VUB` env read is gone.)
    #[must_use]
    pub fn with_vub(mut self, enabled: bool) -> Self {
        self.vub = Some(enabled);
        self
    }

    /// Admit all-integral models with general-integer columns to the MIR
    /// family (the narrowed gate). Default on.
    #[must_use]
    pub fn with_mir_genint(mut self, enabled: bool) -> Self {
        self.mir_genint = Some(enabled);
        self
    }

    /// Screen separation candidates before exact delta derivation. Default on.
    #[must_use]
    pub fn with_sep_screen(mut self, enabled: bool) -> Self {
        self.sep_screen = Some(enabled);
        self
    }

    /// Forrest–Tomlin fast (bounds-check-elided) update path. Default on;
    /// both arms are byte-identical, this is an A/B lane.
    #[must_use]
    pub fn with_ft_fast(mut self, enabled: bool) -> Self {
        self.ft_fast = Some(enabled);
        self
    }

    /// Dense `ftran` fast path. Default on; byte-identical A/B lane.
    #[must_use]
    pub fn with_ftran_fast(mut self, enabled: bool) -> Self {
        self.ftran_fast = Some(enabled);
        self
    }

    /// Sparse `ftran_nz` fast path. Default on; byte-identical A/B lane.
    #[must_use]
    pub fn with_ftran_nz_fast(mut self, enabled: bool) -> Self {
        self.ftran_nz_fast = Some(enabled);
        self
    }

    /// O(m) counting sort for sparse-solve reach sets. Default on; the
    /// comparison sort produces the identical unique order.
    #[must_use]
    pub fn with_countsort(mut self, enabled: bool) -> Self {
        self.countsort = Some(enabled);
        self
    }

    /// Presolve coefficient tightening. Default on.
    #[must_use]
    pub fn with_coef_tighten(mut self, enabled: bool) -> Self {
        self.coef_tighten = Some(enabled);
        self
    }

    /// Static orbitope assembly from symmetry generators. Default on; off
    /// keeps every generator on the per-branch orbit walk (the A/B lane).
    #[must_use]
    pub fn with_orbitope(mut self, enabled: bool) -> Self {
        self.orbitope = Some(enabled);
        self
    }

    /// Forrest–Tomlin growth tolerance (refactorization trigger).
    ///
    /// # Errors
    ///
    /// [`EngineConfigError`] unless `tol` is finite and positive.
    pub fn with_ft_growth_tol(mut self, tol: f64) -> Result<Self, EngineConfigError> {
        self.ft_growth_tol = Some(checked(
            Knob::FtGrowthTol,
            tol,
            f64::MIN_POSITIVE,
            f64::MAX,
        )?);
        Ok(self)
    }

    /// Feasibility-pump restart allowance (`--pump-restarts`).
    ///
    /// `0` skips the pump outright. Unset leaves the engine's own
    /// shape-dependent allowance in force, which is not a single number — so
    /// setting this overrides a *decision*, not just a budget.
    #[must_use]
    pub fn with_pump_restarts(mut self, restarts: usize) -> Self {
        self.pump_restarts = Some(restarts);
        self
    }

    /// Cap on the pins the terminal-salvage dive commits
    /// (`--dive-max-pins`; default uncapped).
    ///
    /// Capping both reproduces a solvable pin set run-to-run and stops paying
    /// for doomed deeper probes. Note this knob is instance-family-tuned by
    /// nature; a principled auto-cap inside the engine is the recorded fix and
    /// this is the interim.
    #[must_use]
    pub fn with_dive_max_pins(mut self, pins: usize) -> Self {
        self.dive_max_pins = Some(pins);
        self
    }

    /// Run dual fixing by lock counting (`--no-dualfix`).
    ///
    /// Default on for models with an identically-zero objective. This is a
    /// **WLOG reduction, not a valid inequality**: it preserves the ANSWER, not
    /// the feasible set ("if a solution exists, one exists with x_j at this
    /// bound"). The UNSAT lane's tree certificate is bought back by re-solving
    /// the caller's own model, so evidence survives — but a consumer that wants
    /// the unreduced model proved directly turns it off here.
    #[must_use]
    pub fn with_dual_fixing(mut self, enabled: bool) -> Self {
        self.dual_fixing = Some(enabled);
        self
    }

    /// Run the AHL kernel reformulation (`--no-kernel-reform`).
    ///
    /// Admits only the isolated shape. A consumer whose models could present an
    /// equality block whose support is entirely integral, and who would rather
    /// not rely on that gate, turns it off here.
    #[must_use]
    pub fn with_kernel_reformulation(mut self, enabled: bool) -> Self {
        self.kernel_reformulation = Some(enabled);
        self
    }

    /// Decouple root reductions from certificate capture
    /// (`EngineEconomics::with_certificate_decoupling(false)`).
    ///
    /// Default on: reductions run even with capture armed, and the artifact is
    /// harvested by re-solving the original model. Off restores the prior
    /// coupling byte-identically — reductions are skipped whenever
    /// [`SolveOpts::with_tree_cert_leaves`] is non-zero, which is the gate a
    /// certificate-requiring consumer was implicitly relying on before.
    #[must_use]
    pub fn with_certificate_decoupling(mut self, enabled: bool) -> Self {
        self.certificate_decoupling = Some(enabled);
        self
    }

    /// Arm the zero-objective feasibility conflict class
    /// (`--no-feas-conflict`).
    ///
    /// Default on. Nogood unit propagation, nogood-guided branching and VSIDS,
    /// gated on the objective being identically zero rather than on model size.
    /// Verdict-neutral search economics; measured 10.96x fewer nodes on that
    /// class.
    #[must_use]
    pub fn with_feasibility_conflict(mut self, enabled: bool) -> Self {
        self.feasibility_conflict = Some(enabled);
        self
    }

    /// Route the COLD ROOT LP to the LU lane inside the measured row band
    /// (`--no-cold-lu`).
    ///
    /// Default on for `m` in the band. Off restores the historical eta-file
    /// cold root byte-for-byte. Verdict-neutral: it changes which optimal
    /// vertex seeds the heuristic chain, and every exit is re-checked.
    #[must_use]
    pub fn with_cold_root_lu(mut self, enabled: bool) -> Self {
        self.cold_root_lu = Some(enabled);
        self
    }

    /// Whether dual fixing is explicitly configured for this solve.
    #[must_use]
    pub fn dual_fixing(&self) -> Option<bool> {
        self.dual_fixing
    }

    /// Whether the kernel reformulation is explicitly configured.
    #[must_use]
    pub fn kernel_reformulation(&self) -> Option<bool> {
        self.kernel_reformulation
    }

    /// Whether certificate decoupling is explicitly configured.
    #[must_use]
    pub fn certificate_decoupling(&self) -> Option<bool> {
        self.certificate_decoupling
    }

    /// Whether the feasibility conflict class is explicitly configured.
    #[must_use]
    pub fn feasibility_conflict(&self) -> Option<bool> {
        self.feasibility_conflict
    }

    /// Whether the cold-root LU band is explicitly configured.
    #[must_use]
    pub fn cold_root_lu(&self) -> Option<bool> {
        self.cold_root_lu
    }

    /// Whether the lattice detector is explicitly configured for this solve.
    #[must_use]
    pub fn lattice(&self) -> Option<bool> {
        self.lattice
    }

    /// Whether the flip-LNS saturation stop is explicitly configured.
    #[must_use]
    pub fn saturation_stop(&self) -> Option<bool> {
        self.saturation_stop
    }

    /// The explicitly configured saturation-stop dry-spell floor.
    #[must_use]
    pub fn saturation_stop_floor(&self) -> Option<Duration> {
        self.saturation_stop_floor.map(Duration::from_secs_f64)
    }

    /// The explicitly configured saturation-stop multiplier.
    #[must_use]
    pub fn saturation_stop_multiplier(&self) -> Option<f64> {
        self.saturation_stop_multiplier
    }

    /// Whether the bloom-cap relaxation is explicitly configured.
    #[must_use]
    pub fn bloom_cap_relaxation(&self) -> Option<bool> {
        self.bloom_cap_relaxation
    }

    /// The explicitly configured absolute flip-LNS window cap.
    #[must_use]
    pub fn flip_lns_cap(&self) -> Option<Duration> {
        self.flip_lns_cap.map(Duration::from_secs_f64)
    }

    /// The explicitly configured flip-LNS budget share.
    #[must_use]
    pub fn flip_lns_share(&self) -> Option<f64> {
        self.flip_lns_share
    }

    /// Whether the pooled re-solver's LU engine is explicitly configured.
    #[must_use]
    pub fn warm_lu(&self) -> Option<bool> {
        self.warm_lu
    }

    /// The explicitly configured presolve budget share.
    #[must_use]
    pub fn presolve_share(&self) -> Option<f64> {
        self.presolve_share
    }

    /// Whether root cuts are explicitly configured.
    #[must_use]
    pub fn cuts(&self) -> Option<bool> {
        self.cuts
    }

    /// The explicitly configured feasibility-pump restart allowance.
    #[must_use]
    pub fn pump_restarts(&self) -> Option<usize> {
        self.pump_restarts
    }

    /// The explicitly configured terminal-salvage dive pin cap.
    #[must_use]
    pub fn dive_max_pins(&self) -> Option<usize> {
        self.dive_max_pins
    }
}

/// Default-off warm-start strategy for complete fixed assignment trees.
///
/// These modes change only how float advice is obtained before exact leaf
/// certification. Root and prefix statuses never contribute evidence. Ordinary
/// leaves exactify `Optimal` duals or `PrimalInfeasible` Farkas multipliers as
/// before. The first configured non-optimal leaf may instead exactify the
/// prefix candidate's cached true-objective duals under the fully fixed leaf;
/// only a strictly sufficient, independently verified row contributes to the
/// returned proof. Local durations are cooperative caps: zero requests an
/// immediate stop poll, finite values are intersected with the outer proof
/// deadline, and `Duration::MAX` removes only the local cap without extending
/// an outer deadline.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum FixedAssignmentTreeWarmStart {
    /// Solve progressively narrower prefixes before the first complete
    /// assignment, changing one split bound per warm solve. The Gray walk is
    /// translated by `start_assignment`, so it starts there while retaining
    /// one-bit transitions and complete coverage. Each prefix is capped by
    /// `prefix_time_limit` and continues primal phase I directly from the
    /// preceding basis; a locally stopped basis remains float advice only.
    /// The first complete proof leaf first attempts to exactify its cached
    /// true-objective row duals, then may continue that stopped primal state.
    /// Either route must pass independent exact leaf verification.
    ProgressivePrefix {
        prefix_time_limit: Duration,
        start_assignment: u8,
    },
    /// Bound the optional root-fast-path search, then bridge progressively to
    /// `start_assignment`.
    ///
    /// If the root reaches `Optimal` within `root_time_limit`, the historical
    /// exact root-row fast path is still attempted. If it stops at the local
    /// limit, its basis is advice only and complete exact leaf harvesting
    /// continues under the session's outer deadline. Each progressive prefix
    /// has its own `prefix_time_limit`.
    RootProbeThenProgressivePrefix {
        root_time_limit: Duration,
        prefix_time_limit: Duration,
        start_assignment: u8,
    },
}

/// Options for a session's solves.
///
/// `#[non_exhaustive]` with builder methods so the engine can grow options
/// without breaking callers.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct SolveOpts {
    /// Absolute wall-clock search deadline. Checked inside solve loops; expiry
    /// stops new search work. The solver may retain a checked `Feasible`
    /// incumbent or rigorous `Bound` from completed progress, and otherwise
    /// returns `Outcome::Unknown { reason: Timeout }`. A bounded post-verdict
    /// certificate-enrichment pass may run beyond this search horizon, so this
    /// is not a strict call-return deadline.
    pub deadline: Option<Instant>,
    /// Per-solve search duration; combines with `deadline` (the earlier wins).
    /// It also sizes bounded post-verdict certificate enrichment, so it remains
    /// visible after the search deadline is pinned and is not a strict
    /// call-return wall. A duration that cannot be represented relative to the
    /// solve start is normalized to no duration cap; an explicit `deadline`
    /// still applies.
    pub time_limit: Option<Duration>,
    /// Per-node time limit for a warm LP attempt in branch-and-bound. When the
    /// limit expires, the node discards its warm-start hint and retries cold
    /// exactly once under the solve's outer deadline. `None` disables the
    /// warm-only limit; it never extends the outer deadline.
    pub node_warm_time_limit: Option<Duration>,
    /// Worker threads a session may use. The exact PB optimization portfolio
    /// consumes this budget when determinism is disabled; native branch-and-
    /// bound remains single-threaded.
    pub threads: u32,
    /// When true (default), identical inputs give identical outcomes
    /// run-to-run.
    pub determinism: bool,
    /// Seed for randomized heuristics (unused while `determinism` holds all
    /// current lanes fixed; reserved for the native engine).
    pub seed: u64,
    /// When true, a certificate-bearing outcome shape missing its required
    /// artifact degrades to `Outcome::Unknown { reason: CertificateUnavailable }`.
    /// This availability policy neither validates public outcome fields nor
    /// makes every surviving claim independently checkable.
    pub require_certificates: bool,
    /// Admit the exact STRUCTURE-RECOGNITION routes (PB projection, direct
    /// CNF, SAT/ReLU recovery, network design, open-domain, hybrid PB/LP) on
    /// an ordinary native check. On by default.
    ///
    /// This exists so the native branch-and-bound lane — the only lane that
    /// emits a root `FarkasCertificate` or a whole-tree
    /// [`crate::MilpInfeasibilityCertificate`] — stays reachable and testable
    /// on models a routed lane would otherwise claim first. Turning it off can
    /// change solved-versus-timeout status and evidence shape because native
    /// search may not decide every model a specialized lane does; it must not
    /// change soundness. `SolveOpts::with_structure_routing(false)` exposes the
    /// native fallback for A/B measurement on that solve/session.
    pub structure_routing: bool,
    /// Bytes the branch-and-bound may RETAIN in its open node set (the
    /// dominant memory at scale: parked warm-start bases). Crossing half the
    /// budget stops new parked nodes from carrying warm hints; crossing the
    /// budget stops the frontier growing at all (depth-first from there, which
    /// holds O(depth)). The SAT/ReLU structure route also treats this as its
    /// total logical plan-plus-proof envelope and declines before entering an
    /// unmetered fallback. Allocator transients and SAT solver working state
    /// still require the CLI/process RSS envelope documented by the harness.
    /// Running into the budget can cost time and can degrade an exhausted
    /// search to `Feasible`/`Unknown` — never a wrong verdict. `None` disables
    /// these guards.
    pub memory_budget: Option<usize>,
    /// Leaf budget for capturing a whole-tree
    /// [`crate::MilpInfeasibilityCertificate`] on `Infeasible` verdicts from
    /// the native branch-and-bound. The capture is fail-closed: a tree that
    /// needs more leaves, outlives the deadline, or cannot be re-derived in
    /// the caller's model frame yields `tree_cert: None` and the verdict is
    /// unaffected. `0` disables capture entirely.
    pub tree_cert_leaves: usize,
    /// Diagnostic warm start: a whitespace `col value` file whose integer
    /// columns are pinned and completed exactly before the search starts.
    /// Verified feasible before use; a bad seed is discarded, never believed.
    /// (B13: was the never-set `AY_MILP_SEED_SOL` env var.)
    pub seed_solution_file: Option<std::path::PathBuf>,
    /// Admit the range-logical triangular-crash LP path for this solve.
    ///
    /// This is an advice-only, default-off path choice. The historical exact
    /// `AY_MILP_RANGE_LOGICAL_CRASH=1` process-environment opt-in remains an
    /// independent compatibility fallback.
    pub(crate) range_logical_triangular_crash: bool,
    /// Per-session override for the cold affine-chain distress-probe iteration
    /// budget. `None` preserves the historical
    /// `the chain-probe knob`/20,000-iteration policy; `Some(0)` disables the
    /// probe for LPs lowered by this session.
    pub(crate) chain_distress_probe_iters: Option<u64>,
    /// Default-off float-basis strategy for the complete fixed assignment-tree
    /// proof API. This is advice only and is deliberately not consulted by the
    /// target-FSB or adaptive tree APIs.
    pub(crate) fixed_assignment_tree_warm_start: Option<FixedAssignmentTreeWarmStart>,
    /// Per-solve search economics. Every field defaults to *no opinion*, so
    /// these options resolve exactly as they did before the carrier existed.
    pub(crate) engine: EngineEconomics,
    /// Measurement-only fallback carrier for models rebuilt rather than
    /// cloned during one top-level native MILP solve. Cleared when the
    /// owning/nested `BabSession::check` returns.
    pub(crate) ft_adoption_solve_latch: Option<crate::sepstat::FtAdoptionSolveLatch>,
}

impl Default for SolveOpts {
    fn default() -> Self {
        Self {
            deadline: None,
            time_limit: None,
            node_warm_time_limit: None,
            threads: 1,
            determinism: true,
            seed: 0,
            require_certificates: false,
            structure_routing: true,
            memory_budget: Some(2 << 30), // 2 GiB
            tree_cert_leaves: 256,
            seed_solution_file: None,
            range_logical_triangular_crash: false,
            chain_distress_probe_iters: None,
            fixed_assignment_tree_warm_start: None,
            engine: EngineEconomics::new(),
            ft_adoption_solve_latch: None,
        }
    }
}

impl SolveOpts {
    /// Default options.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Set the absolute search deadline described by [`Self::deadline`].
    /// Bounded post-verdict certificate enrichment may extend call-return time.
    #[must_use]
    pub fn with_deadline(mut self, deadline: Instant) -> Self {
        self.deadline = Some(deadline);
        self
    }

    /// Set the search duration described by [`Self::time_limit`]. It also sizes
    /// bounded post-verdict certificate enrichment. An unrepresentable relative
    /// deadline is normalized as documented on that field.
    #[must_use]
    pub fn with_time_limit(mut self, limit: Duration) -> Self {
        self.time_limit = Some(limit);
        self
    }

    /// Set (or disable, with `None`) the per-node warm LP time limit.
    ///
    /// A zero duration is normalized to `None`, matching the historical
    /// zero-means-disabled configuration.
    #[must_use]
    pub fn with_node_warm_time_limit(mut self, limit: Option<Duration>) -> Self {
        self.node_warm_time_limit = limit.filter(|limit| !limit.is_zero());
        self
    }

    /// Set the thread budget.
    #[must_use]
    pub fn with_threads(mut self, threads: u32) -> Self {
        self.threads = threads;
        self
    }

    /// Set determinism.
    #[must_use]
    pub fn with_determinism(mut self, determinism: bool) -> Self {
        self.determinism = determinism;
        self
    }

    /// Set the heuristic seed.
    #[must_use]
    pub fn with_seed(mut self, seed: u64) -> Self {
        self.seed = seed;
        self
    }

    /// Require artifacts on outcome shapes that define a certificate requirement.
    ///
    /// This is availability policy, not proof: [`crate::EvidenceShape::FieldsPresent`]
    /// still must pass [`crate::Outcome::check_against`] before it is authoritative.
    #[must_use]
    pub fn with_require_certificates(mut self, require: bool) -> Self {
        self.require_certificates = require;
        self
    }

    /// Admit or refuse the exact structure-recognition routes on an ordinary
    /// native check.
    ///
    /// Refusing them pins the solve on native branch-and-bound, which is the
    /// only lane that exports a root Farkas or a whole-tree case-split
    /// certificate. Use it to test that lane directly, or to A/B a routed
    /// answer against the general engine. See [`SolveOpts::structure_routing`].
    #[must_use]
    pub fn with_structure_routing(mut self, enabled: bool) -> Self {
        self.structure_routing = enabled;
        self
    }

    /// Set (or disable, with `None`) the open-set and routed logical memory
    /// budget in bytes. See [`SolveOpts::memory_budget`].
    #[must_use]
    pub fn with_memory_budget(mut self, bytes: Option<usize>) -> Self {
        self.memory_budget = bytes;
        self
    }

    /// Set the tree-certificate leaf budget (`0` disables capture).
    #[must_use]
    pub fn with_tree_cert_leaves(mut self, leaves: usize) -> Self {
        self.tree_cert_leaves = leaves;
        self
    }

    /// Seed the search from a `col value` solution file (see
    /// [`SolveOpts::seed_solution_file`]).
    #[must_use]
    pub fn with_seed_solution_file(mut self, path: std::path::PathBuf) -> Self {
        self.seed_solution_file = Some(path);
        self
    }

    /// Request the range-logical triangular-crash LP path for this solve.
    ///
    /// The option is scoped to sessions built from these options and does not
    /// mutate process environment or change the global default.
    #[must_use]
    pub fn with_range_logical_triangular_crash(mut self) -> Self {
        self.range_logical_triangular_crash = true;
        self
    }

    /// Whether this option explicitly requests the range-logical
    /// triangular-crash LP path.
    ///
    /// This reports only the typed per-session setting. The solver separately
    /// honors the historical exact `AY_MILP_RANGE_LOGICAL_CRASH=1`
    /// environment opt-in for compatibility.
    #[must_use]
    pub fn range_logical_triangular_crash(&self) -> bool {
        self.range_logical_triangular_crash
    }

    /// Override the cold affine-chain distress-probe iteration budget for LPs
    /// lowered by this session.
    ///
    /// `None` preserves the historical process policy
    /// (`the chain-probe knob`, defaulting to 20,000 iterations). `Some(0)`
    /// disables the probe without mutating process-global environment.
    #[must_use]
    pub fn with_chain_distress_probe_iters(mut self, iters: Option<u64>) -> Self {
        self.chain_distress_probe_iters = iters;
        self
    }

    /// The typed per-session chain distress-probe override.
    ///
    /// This excludes the historical environment/default fallback, which the
    /// simplex resolves only when no typed override is present.
    #[must_use]
    pub fn chain_distress_probe_iters(&self) -> Option<u64> {
        self.chain_distress_probe_iters
    }

    /// Select a default-off warm-start strategy for complete fixed assignment
    /// trees.
    ///
    /// This option is proof-neutral: root probes and prefix solves supply float
    /// bases only, including when their local cap yields `Stopped`. Final
    /// leaves retain the same exactification and independent
    /// certificate-verification requirements as the default path.
    #[must_use]
    pub fn with_fixed_assignment_tree_warm_start(
        mut self,
        strategy: Option<FixedAssignmentTreeWarmStart>,
    ) -> Self {
        self.fixed_assignment_tree_warm_start = strategy;
        self
    }

    /// The typed per-session fixed assignment-tree warm-start strategy.
    #[must_use]
    pub fn fixed_assignment_tree_warm_start(&self) -> Option<FixedAssignmentTreeWarmStart> {
        self.fixed_assignment_tree_warm_start
    }

    /// Configure per-solve search economics.
    ///
    /// The settings are scoped to solves run from these options: they are
    /// carried on the solve, not written to the process, so two concurrent
    /// sessions can differ and neither can disturb the other. They outrank any
    /// `AY_MILP_*` variable in the environment.
    ///
    /// ```
    /// # use ay_milp::{EngineEconomics, SolveOpts};
    /// # fn main() -> Result<(), ay_milp::EngineConfigError> {
    /// let opts = SolveOpts::new().with_engine(
    ///     EngineEconomics::new()
    ///         .with_lattice(false)
    ///         .with_cuts(false)
    ///         .with_presolve_share(0.02)?
    ///         .with_dive_max_pins(16),
    /// );
    /// # let _ = opts;
    /// # Ok(())
    /// # }
    /// ```
    #[must_use]
    pub fn with_engine(mut self, engine: EngineEconomics) -> Self {
        self.engine = engine;
        self
    }

    /// The per-solve search economics configured for these options.
    #[must_use]
    pub fn engine(&self) -> EngineEconomics {
        self.engine
    }

    pub(crate) fn ft_adoption_solve_latch(&self) -> Option<crate::sepstat::FtAdoptionSolveLatch> {
        self.ft_adoption_solve_latch.clone()
    }

    pub(crate) fn set_ft_adoption_solve_latch(
        &mut self,
        latch: crate::sepstat::FtAdoptionSolveLatch,
    ) {
        self.ft_adoption_solve_latch = Some(latch);
    }

    #[must_use]
    pub(crate) fn with_ft_adoption_solve_latch(
        mut self,
        latch: Option<crate::sepstat::FtAdoptionSolveLatch>,
    ) -> Self {
        self.ft_adoption_solve_latch = latch;
        self
    }

    pub(crate) fn clear_ft_adoption_solve_latch(&mut self) {
        self.ft_adoption_solve_latch = None;
    }

    /// The effective deadline as of `now`: the earlier of `deadline` and a
    /// representable `now + time_limit`. An overflowing relative limit means
    /// no duration cap; it does not suppress an explicit absolute deadline.
    #[must_use]
    pub fn effective_deadline(&self, now: Instant) -> Option<Instant> {
        let from_limit = self.time_limit.and_then(|limit| now.checked_add(limit));
        match (self.deadline, from_limit) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (a, b) => a.or(b),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    include!("opts/deadline_tests.rs");

    #[test]
    fn engine_economics_default_to_no_opinion() {
        let engine = SolveOpts::new().engine();
        assert!(engine.profile().is_empty());
        assert_eq!(engine.lattice(), None);
        assert_eq!(engine.saturation_stop(), None);
        assert_eq!(engine.saturation_stop_floor(), None);
        assert_eq!(engine.saturation_stop_multiplier(), None);
        assert_eq!(engine.bloom_cap_relaxation(), None);
        assert_eq!(engine.flip_lns_cap(), None);
        assert_eq!(engine.flip_lns_share(), None);
        assert_eq!(engine.warm_lu(), None);
        assert_eq!(engine.presolve_share(), None);
        assert_eq!(engine.cuts(), None);
        assert_eq!(engine.pump_restarts(), None);
        assert_eq!(engine.dive_max_pins(), None);
    }

    /// The twelve settings a consumer pins today, in one chain, with every
    /// value read back. This is the shape `ay_lib.rs` had to spell as twelve
    /// `set_var` calls on the process environment.
    #[test]
    fn engine_economics_round_trip_through_the_builder() -> Result<(), EngineConfigError> {
        let engine = EngineEconomics::new()
            .with_lattice(false)
            .with_saturation_stop(false)
            .with_saturation_stop_floor(Duration::from_secs(15))
            .with_saturation_stop_multiplier(1.5)?
            .with_bloom_cap_relaxation(false)
            .with_flip_lns_cap(Duration::from_mins(15))
            .with_flip_lns_share(0.25)?
            .with_warm_lu(true)
            .with_presolve_share(0.02)?
            .with_cuts(false)
            .with_pump_restarts(0)
            .with_dive_max_pins(16);

        assert_eq!(engine.lattice(), Some(false));
        assert_eq!(engine.saturation_stop(), Some(false));
        assert_eq!(
            engine.saturation_stop_floor(),
            Some(Duration::from_secs(15))
        );
        assert_eq!(engine.saturation_stop_multiplier(), Some(1.5));
        assert_eq!(engine.bloom_cap_relaxation(), Some(false));
        assert_eq!(engine.flip_lns_cap(), Some(Duration::from_mins(15)));
        assert_eq!(engine.flip_lns_share(), Some(0.25));
        assert_eq!(engine.warm_lu(), Some(true));
        assert_eq!(engine.presolve_share(), Some(0.02));
        assert_eq!(engine.cuts(), Some(false));
        assert_eq!(engine.pump_restarts(), Some(0));
        assert_eq!(engine.dive_max_pins(), Some(16));
        Ok(())
    }

    /// The positive-sense public surface must lower to the negative-sense
    /// engine knobs, and it is the resolved knob — not the field — that the
    /// solver reads. An inversion dropped here would be invisible in every
    /// getter and wrong in every solve.
    #[test]
    fn positive_setters_lower_to_the_negative_kill_switches() -> Result<(), EngineConfigError> {
        let engine = EngineEconomics::new()
            .with_lattice(false)
            .with_saturation_stop(false)
            .with_bloom_cap_relaxation(false)
            .with_cuts(false)
            .with_warm_lu(true)
            .with_dive_max_pins(16)
            .with_pump_restarts(0)
            .with_presolve_share(0.02)?;
        let _active = crate::tune::activate_caller(engine.profile());
        assert!(crate::tune::on(Knob::NoLattice));
        assert!(crate::tune::on(Knob::NoSatStop));
        assert!(crate::tune::on(Knob::NoBloomRelax));
        assert!(crate::tune::on(Knob::NoCuts));
        assert!(crate::tune::on(Knob::WarmLu));
        assert_eq!(crate::tune::count(Knob::DiveMaxPins, usize::MAX), 16);
        assert_eq!(crate::tune::count_opt(Knob::PumpRestarts), Some(0));
        assert_eq!(crate::tune::real(Knob::PresolveShare, 0.35), 0.02);

        let on = EngineEconomics::new()
            .with_lattice(true)
            .with_cuts(true)
            .with_warm_lu(false);
        let _active = crate::tune::activate_caller(on.profile());
        assert!(!crate::tune::on(Knob::NoLattice));
        assert!(!crate::tune::on(Knob::NoCuts));
        assert!(!crate::tune::on(Knob::WarmLu));
        Ok(())
    }

    /// Malformed input is refused at construction and cannot reach a solve.
    /// Every value here used to be accepted from the environment, and the two
    /// negatives used to panic `Duration::mul_f64`/`from_secs_f64` mid-solve.
    #[test]
    fn out_of_range_settings_are_rejected_not_clamped() {
        assert_eq!(
            EngineEconomics::new().with_presolve_share(1.5),
            Err(EngineConfigError::OutOfRange {
                knob: "presolve-share",
                value: 1.5,
                low: 0.0,
                high: 1.0,
            })
        );
        assert_eq!(
            EngineEconomics::new().with_flip_lns_share(-0.25),
            Err(EngineConfigError::OutOfRange {
                knob: "flip-share",
                value: -0.25,
                low: 0.0,
                high: 1.0,
            })
        );
        assert_eq!(
            EngineEconomics::new().with_saturation_stop_multiplier(-1.0),
            Err(EngineConfigError::OutOfRange {
                knob: "sat-stop-mult",
                value: -1.0,
                low: 0.0,
                high: MAX_KNOB_SECS,
            })
        );
        assert_eq!(
            EngineEconomics::new().with_presolve_share(f64::INFINITY),
            Err(EngineConfigError::NotFinite {
                knob: "presolve-share",
                value: f64::INFINITY,
            })
        );
        assert!(matches!(
            EngineEconomics::new().with_saturation_stop_multiplier(f64::NAN),
            Err(EngineConfigError::NotFinite { .. })
        ));
        // A rejected setter returns the error INSTEAD of a value, so there is
        // no half-configured `EngineEconomics` to carry into a solve.
        assert_eq!(SolveOpts::new().engine(), EngineEconomics::new());
    }

    /// `Duration::MAX` is an unambiguous "no cap" and must not become a value
    /// that panics `Duration::from_secs_f64` at the consuming site.
    #[test]
    fn an_unbounded_duration_clamps_instead_of_overflowing() {
        let engine = EngineEconomics::new()
            .with_flip_lns_cap(Duration::MAX)
            .with_saturation_stop_floor(Duration::MAX);
        let cap = engine.flip_lns_cap().expect("set");
        assert_eq!(cap, Duration::from_secs_f64(MAX_KNOB_SECS));
        assert!(engine.saturation_stop_floor().is_some());
    }

    /// END TO END, THROUGH A REAL SOLVE. The recipe a consumer pins reaches
    /// the engine, and the verdict is the same exact rational either way.
    ///
    /// This is the test that would catch the plumbing being wired to nothing:
    /// `activate_caller` is installed at the branch-and-bound entry, so a
    /// `SolveOpts` carrying twelve settings must produce the same optimum as
    /// one carrying none, on a model whose optimum is known by inspection.
    /// Both directions are exercised — every switch off, then every switch on —
    /// because a knob that is honoured in only one direction is a knob that is
    /// not honoured.
    #[test]
    fn a_configured_solve_returns_the_same_exact_optimum() -> Result<(), EngineConfigError> {
        use crate::model::{Model, Sense};
        use crate::Outcome;

        // min -3a - 2b - 4c  s.t.  a + b + c <= 2, all binary.  Optimum: pick
        // c and a, value -7.
        let mut m = Model::new();
        let a = m.add_binary_col();
        let b = m.add_binary_col();
        let c = m.add_binary_col();
        m.add_row(f64::NEG_INFINITY, 2.0, &[(a, 1.0), (b, 1.0), (c, 1.0)]);
        m.set_objective(&[(a, -3.0), (b, -2.0), (c, -4.0)], Sense::Minimize);

        let want = num_rational::BigRational::from_integer((-7).into());
        let recipes = [
            SolveOpts::new(),
            SolveOpts::new().with_engine(
                EngineEconomics::new()
                    .with_lattice(false)
                    .with_saturation_stop(false)
                    .with_saturation_stop_floor(Duration::from_secs(15))
                    .with_saturation_stop_multiplier(1.5)?
                    .with_bloom_cap_relaxation(false)
                    .with_flip_lns_cap(Duration::from_mins(15))
                    .with_flip_lns_share(0.25)?
                    .with_warm_lu(true)
                    .with_presolve_share(0.02)?
                    .with_cuts(false)
                    .with_pump_restarts(0)
                    .with_dive_max_pins(16),
            ),
            SolveOpts::new().with_engine(
                EngineEconomics::new()
                    .with_lattice(true)
                    .with_saturation_stop(true)
                    .with_bloom_cap_relaxation(true)
                    .with_warm_lu(false)
                    .with_cuts(true)
                    .with_presolve_share(1.0)?,
            ),
        ];
        for (i, opts) in recipes.iter().enumerate() {
            match crate::bab::solve_milp(&m, opts) {
                Outcome::Optimal { value, .. } => {
                    assert_eq!(value, want, "recipe {i} must land the same optimum");
                }
                other => panic!("recipe {i}: expected Optimal, got {other:?}"),
            }
        }
        Ok(())
    }

    /// Per-`SolveOpts`, not per-process: configuring one set of options cannot
    /// reach another.
    #[test]
    fn engine_economics_are_scoped_to_their_options() {
        let default = SolveOpts::new();
        let configured = default
            .clone()
            .with_engine(EngineEconomics::new().with_cuts(false));
        assert_eq!(configured.engine().cuts(), Some(false));
        assert_eq!(
            default.engine().cuts(),
            None,
            "building a configured sibling must not mutate the original options"
        );
    }

    #[test]
    fn range_logical_triangular_crash_defaults_off_and_is_scoped() {
        let default = SolveOpts::new();
        let explicit = default.clone().with_range_logical_triangular_crash();

        assert!(!default.range_logical_triangular_crash());
        assert!(explicit.range_logical_triangular_crash());
        assert!(
            !default.range_logical_triangular_crash(),
            "building an opted-in sibling must not change the original options"
        );
    }

    #[test]
    fn chain_distress_probe_iters_defaults_to_historical_policy() {
        assert_eq!(SolveOpts::new().chain_distress_probe_iters(), None);
    }

    #[test]
    fn chain_distress_probe_iters_builder_is_typed_and_scoped() {
        let default = SolveOpts::new();
        let finite = default
            .clone()
            .with_chain_distress_probe_iters(Some(12_345));
        let disabled = default.clone().with_chain_distress_probe_iters(Some(0));

        assert_eq!(finite.chain_distress_probe_iters(), Some(12_345));
        assert_eq!(disabled.chain_distress_probe_iters(), Some(0));
        assert_eq!(
            finite
                .with_chain_distress_probe_iters(None)
                .chain_distress_probe_iters(),
            None
        );
        assert_eq!(
            default.chain_distress_probe_iters(),
            None,
            "building configured siblings must not mutate the original options"
        );
    }

    #[test]
    fn fixed_assignment_tree_warm_start_defaults_off_and_is_scoped() {
        let default = SolveOpts::new();
        let bridge = default.clone().with_fixed_assignment_tree_warm_start(Some(
            FixedAssignmentTreeWarmStart::ProgressivePrefix {
                prefix_time_limit: Duration::from_millis(100),
                start_assignment: 1,
            },
        ));
        let probe = default.clone().with_fixed_assignment_tree_warm_start(Some(
            FixedAssignmentTreeWarmStart::RootProbeThenProgressivePrefix {
                root_time_limit: Duration::from_millis(250),
                prefix_time_limit: Duration::from_millis(100),
                start_assignment: 9,
            },
        ));

        assert_eq!(default.fixed_assignment_tree_warm_start(), None);
        assert_eq!(
            bridge.fixed_assignment_tree_warm_start(),
            Some(FixedAssignmentTreeWarmStart::ProgressivePrefix {
                prefix_time_limit: Duration::from_millis(100),
                start_assignment: 1,
            })
        );
        assert_eq!(
            probe.fixed_assignment_tree_warm_start(),
            Some(
                FixedAssignmentTreeWarmStart::RootProbeThenProgressivePrefix {
                    root_time_limit: Duration::from_millis(250),
                    prefix_time_limit: Duration::from_millis(100),
                    start_assignment: 9,
                }
            )
        );
        assert_eq!(
            probe
                .with_fixed_assignment_tree_warm_start(None)
                .fixed_assignment_tree_warm_start(),
            None
        );
        assert_eq!(
            default.fixed_assignment_tree_warm_start(),
            None,
            "building configured siblings must not mutate the original options"
        );
    }
}
