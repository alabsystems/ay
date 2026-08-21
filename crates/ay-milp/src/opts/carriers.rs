// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Carriers for the knobs the reader-without-writer census found unreachable.
//!
//! # What this file repairs
//!
//! Every knob below had a READER on the solve path and NO WRITER anywhere: no
//! [`EngineEconomics`] field, no builder, no `engine_cli` entry. `mps_solve`'s
//! `Flags::parse` now refuses a bare `--x` with no table entry; before that fix,
//! passing one parsed cleanly, changed nothing, and mislabeled the result.
//! That is measurement rule R7's vacuous null, and this campaign has paid for it
//! four times already (`--root-cuts-per-round`, `--gmi-rounds`,
//! `--eager-perturb-mode`, `--no-float`). `tests/knob_census.rs` is the gate that
//! stops incident five; this module is the repair for the backlog it found.
//!
//! # Every carrier here is `None` by default
//!
//! Adding a carrier cannot move a compiled default: an unset `Option` writes
//! nothing into the [`Profile`], so every accessor resolves exactly as it did
//! before this file existed. The receipts for that are the deterministic MILP
//! four (gt2 / mas76 / pk1 / p0548 node counts) taken before and after.
//!
//! # Negative-sense knobs keep their spelling
//!
//! Same convention as `profile.rs`: a `No*` knob keeps the name an operator
//! already types, the public builder is positive-sense, and the single inversion
//! happens here.

use crate::tune::{Knob, Profile, Setting};

use super::config::{checked, MAX_KNOB_SECS};
use super::{EngineConfigError, EngineEconomics};

impl EngineEconomics {
    /// Objective-singleton substitution (`singleton_sub_enabled`, bab.rs). Opt-in: measured to worsen AY's branching tree on network LPs even though Gurobi profits.
    ///
    /// Flag: `--singleton-sub`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_singleton_sub(mut self, enabled: bool) -> Self {
        self.singleton_sub = Some(enabled);
        self
    }
    /// Separate node cuts WITHOUT waiting for an incumbent. The soundness guard tests need it; the production gate is incumbent-first.
    ///
    /// Flag: `--node-cut-eager`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_node_cut_eager(mut self, enabled: bool) -> Self {
        self.node_cut_eager = Some(enabled);
        self
    }
    /// Exact at-most-one multiway branching (bab.rs `amo_multiway_branch_on`). Experimental arm; fails closed against a dynamic orbitope.
    ///
    /// Flag: `--amo-multiway`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_amo_multiway(mut self, enabled: bool) -> Self {
        self.amo_multiway = Some(enabled);
        self
    }
    /// Per-node reduced-cost fixing (`node_rc_enabled`, bab.rs). Opt-in measurement device.
    ///
    /// Flag: `--node-rc`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_node_rc(mut self, enabled: bool) -> Self {
        self.node_rc = Some(enabled);
        self
    }
    /// The reduced-cost fixing cap guard (bab.rs:255). `--no-rc-cap-guard` restores the unguarded caps, which is the A/B arm the 1e12 factor was measured on.
    ///
    /// Flag: `--no-rc-cap-guard`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_rc_cap_guard(mut self, enabled: bool) -> Self {
        self.rc_cap_guard = Some(enabled);
        self
    }
    /// Force the triangular crash regardless of LP size (`force_tri_crash`, simplex.rs).
    ///
    /// Flag: `--tri-crash-all`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_tri_crash_all(mut self, enabled: bool) -> Self {
        self.tri_crash_all = Some(enabled);
        self
    }
    /// Symmetry-aware branch selection (bab.rs:23954). DEFAULT ON — the reader is `unwrap_or(true)`, so this needs both senses to be an A/B lever.
    ///
    /// Flag: `--sym-branch` / `--no-sym-branch`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_sym_branch(mut self, enabled: bool) -> Self {
        self.sym_branch = Some(enabled);
        self
    }
    /// Exact box-stabilizer enumeration in the walk lane (symmetry.rs).
    ///
    /// Flag: `--stab-orbit`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_stab_orbit(mut self, enabled: bool) -> Self {
        self.stab_orbit = Some(enabled);
        self
    }
    /// Dynamic orbitopal fixing: propagate lex order against the branching order taken rather than the static root order.
    ///
    /// Flag: `--orbitope-dyn`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_orbitope_dyn(mut self, enabled: bool) -> Self {
        self.orbitope_dyn = Some(enabled);
        self
    }
    /// The tree-bound floor (bab.rs:25811). `--no-tree-floor` restores the pre-floor aggregation, the arm the floor was measured against.
    ///
    /// Flag: `--no-tree-floor`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_tree_floor(mut self, enabled: bool) -> Self {
        self.tree_floor = Some(enabled);
        self
    }
    /// Report a bound from an interrupted no-incumbent tree. `--no-tree-bound-outcome` restores the prior `Unknown`, which is the A/B arm.
    ///
    /// Flag: `--no-tree-bound-outcome`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_tree_bound_outcome(mut self, enabled: bool) -> Self {
        self.tree_bound_outcome = Some(enabled);
        self
    }
    /// The root proof floor kept for the global claim (bab.rs:25276).
    ///
    /// Flag: `--no-root-floor`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_root_floor(mut self, enabled: bool) -> Self {
        self.root_floor = Some(enabled);
        self
    }
    /// Reduce a greedy cover to a MINIMAL cover before lifting (cuts.rs). Sound, stronger cut, measured net-neutral-to-negative — opt-in.
    ///
    /// Flag: `--cover-minimal`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_cover_minimal(mut self, enabled: bool) -> Self {
        self.cover_minimal = Some(enabled);
        self
    }
    /// Conflict-clique branching supports (bab.rs `conflict_cliques`). Returns an empty set unless opted in.
    ///
    /// Flag: `--gub-clique`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_gub_clique(mut self, enabled: bool) -> Self {
        self.gub_clique = Some(enabled);
        self
    }
    /// Per-cut GMI trace lines (sepstat.rs). Diagnostic; also reachable via `--trace`, which is why it survived without a carrier.
    ///
    /// Flag: `--gmi-cut-trace`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_gmi_cut_trace(mut self, enabled: bool) -> Self {
        self.gmi_cut_trace = Some(enabled);
        self
    }
    /// Conditional coefficient tightening in presolve. Its own comment says both arms must stay live for re-measurement; without a carrier only one arm existed.
    ///
    /// Flag: `--cond-tighten`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_cond_tighten(mut self, enabled: bool) -> Self {
        self.cond_tighten = Some(enabled);
        self
    }
    /// mod-k covering cuts (`separate_covering_modk`, cuts.rs).
    ///
    /// Flag: `--mod-k`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_mod_k(mut self, enabled: bool) -> Self {
        self.mod_k = Some(enabled);
        self
    }
    /// Per-row trace of the knapsack complementation search (cuts.rs). Diagnostic.
    ///
    /// Flag: `--knap-dbg`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_knap_dbg(mut self, enabled: bool) -> Self {
        self.knap_dbg = Some(enabled);
        self
    }
    /// Try the cold dual start on EVERY LP shape, not just wide-tall (simplex.rs).
    ///
    /// Flag: `--cold-dual-all`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_cold_dual_all(mut self, enabled: bool) -> Self {
        self.cold_dual_all = Some(enabled);
        self
    }
    /// Warm-started root cut-round re-optimisation (bab.rs:6841).
    ///
    /// Flag: `--cut-warm`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_cut_warm(mut self, enabled: bool) -> Self {
        self.cut_warm = Some(enabled);
        self
    }
    /// RLT product cuts (bab.rs:7628, `separate_rlt`). Named in the campaign brief as a family that could never be switched on.
    ///
    /// Flag: `--rlt`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_rlt(mut self, enabled: bool) -> Self {
        self.rlt = Some(enabled);
        self
    }
    /// Commit a `Stopped` dive side rather than treating it as refuted (bab.rs).
    ///
    /// Flag: `--dive-commit-stopped`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_dive_commit_stopped(mut self, enabled: bool) -> Self {
        self.dive_commit_stopped = Some(enabled);
        self
    }
    /// Hand the root Candidate to the root node as a prepared relaxation. `--no-root-warm` restores the duplicate solve so it can be A/B'd.
    ///
    /// Flag: `--no-root-warm`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_root_warm(mut self, enabled: bool) -> Self {
        self.root_warm = Some(enabled);
        self
    }
    /// Orbitope-aligned branching (bab.rs:23140).
    ///
    /// Flag: `--orbitope-branch`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_orbitope_branch(mut self, enabled: bool) -> Self {
        self.orbitope_branch = Some(enabled);
        self
    }
    /// Joint orbitope x row propagation fixpoint (bab.rs:23154).
    ///
    /// Flag: `--orbitope-ilv`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_orbitope_ilv(mut self, enabled: bool) -> Self {
        self.orbitope_ilv = Some(enabled);
        self
    }
    /// Branching that completes the dynamic orbitope sequence's open positions first (bab.rs:23156).
    ///
    /// Flag: `--orbitope-branch-dyn`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_orbitope_branch_dyn(mut self, enabled: bool) -> Self {
        self.orbitope_branch_dyn = Some(enabled);
        self
    }
    /// LOCAL bound-substituted MIR on the node box (bab.rs:23432).
    ///
    /// Flag: `--node-cut-local`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_node_cut_local(mut self, enabled: bool) -> Self {
        self.node_cut_local = Some(enabled);
        self
    }
    /// The f64 scout that pre-filters conditional-tightening candidates (presolve.rs:1132). `--no-cond-scout` runs the exact lane on every binary.
    ///
    /// Flag: `--no-cond-scout`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_cond_scout(mut self, enabled: bool) -> Self {
        self.cond_scout = Some(enabled);
        self
    }
    /// The certified hybrid PB/LP route (session.rs:8875).
    ///
    /// Flag: `--hybrid-pb-lp`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_hybrid_pb_lp(mut self, enabled: bool) -> Self {
        self.hybrid_pb_lp = Some(enabled);
        self
    }
    /// The allocation/time attribution dump. `examples/mps_solve.rs` documents it as `the attrib knob` and had no way to set it.
    ///
    /// Flag: `--attrib`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_attrib(mut self, enabled: bool) -> Self {
        self.attrib = Some(enabled);
        self
    }
    /// The per-region allocation census probes (feature `acensus`; the `alloc_census` example is the only consumer).
    ///
    /// Flag: `--acensus`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_acensus(mut self, enabled: bool) -> Self {
        self.acensus = Some(enabled);
        self
    }
    /// The SCIP-style hybrid branching term (bab.rs `hybrid_on`).
    ///
    /// Flag: `--hybrid-term`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_hybrid_term(mut self, enabled: bool) -> Self {
        self.hybrid_term = Some(enabled);
        self
    }
    /// LP-rank ordering of root probe candidates. `--root-probe-no-lp-rank` takes the unranked order, the arm the ranking was measured against.
    ///
    /// Flag: `--root-probe-no-lp-rank`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_root_probe_lp_rank(mut self, enabled: bool) -> Self {
        self.root_probe_lp_rank = Some(enabled);
        self
    }
    /// The market-split propagation dive (bab.rs:25437). Named in the campaign brief.
    ///
    /// Flag: `--ms-dive`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_ms_dive(mut self, enabled: bool) -> Self {
        self.ms_dive = Some(enabled);
        self
    }
    /// The mas74-class plunge gate. DEFAULT ON (`unwrap_or(true)`), so it needs both senses to be an A/B lever.
    ///
    /// Flag: `--mas74-plunge` / `--no-mas74-plunge`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_mas74_plunge(mut self, enabled: bool) -> Self {
        self.mas74_plunge = Some(enabled);
        self
    }
    /// The relax-and-lift cover family (cuts/relax_lift.rs). Named in the campaign brief.
    ///
    /// Flag: `--relax-lift`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_relax_lift(mut self, enabled: bool) -> Self {
        self.relax_lift = Some(enabled);
        self
    }
    /// Force Devex pricing from iteration 0 regardless of LP shape (simplex.rs:10444). Distinct from `--no-devex`, which disables Devex entirely.
    ///
    /// Flag: `--devex`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_force_devex(mut self, enabled: bool) -> Self {
        self.force_devex = Some(enabled);
        self
    }
    /// The block-triangular bump refactorization lane (simplex.rs `bump_btf_env`).
    ///
    /// Flag: `--bump-btf`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_bump_btf(mut self, enabled: bool) -> Self {
        self.bump_btf = Some(enabled);
        self
    }
    /// Cut slots reserved per node (bab.rs `cut_slot_count`). ALSO the master opt-in for node separation: `node_cuts_opted_in` at bab.rs:23219 tests whether this is set at all.
    ///
    /// Flag: `--node-cut-slots <n>`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_node_cut_slots(mut self, value: usize) -> Self {
        self.node_cut_slots = Some(value);
        self
    }
    /// Minimum node interval between separation attempts.
    ///
    /// Flag: `--node-cut-every <n>`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_node_cut_every(mut self, value: usize) -> Self {
        self.node_cut_every = Some(value);
        self
    }
    /// Node-GMI family bitmask (0 = off). Named in the campaign brief.
    ///
    /// Flag: `--node-gmi <n>`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_node_gmi(mut self, value: usize) -> Self {
        self.node_gmi = Some(value);
        self
    }
    /// Node interval between node-GMI visits (default 500).
    ///
    /// Flag: `--node-gmi-every <n>`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_node_gmi_every(mut self, value: usize) -> Self {
        self.node_gmi_every = Some(value);
        self
    }
    /// LP equilibration mode (`equil_mode`, simplex.rs): 1 or 2 select a scaling lane, anything else is off.
    ///
    /// Flag: `--scale <n>`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_scale(mut self, value: usize) -> Self {
        self.scale = Some(value);
        self
    }
    /// Cap a root cut round at its `n` deepest rows; `0` means no cap.
    ///
    /// Flag: `--cut-topk <n>`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_cut_topk(mut self, value: usize) -> Self {
        self.cut_topk = Some(value);
        self
    }
    /// Per-probe dual iteration cap for tall-LP strong branching.
    ///
    /// Flag: `--sb-probe-iters <n>`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_sb_probe_iters(mut self, value: usize) -> Self {
        self.sb_probe_iters = Some(value);
        self
    }
    /// Candidate cap for root implication probing.
    ///
    /// Flag: `--root-probe-cap <n>`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_root_probe_cap(mut self, value: usize) -> Self {
        self.root_probe_cap = Some(value);
        self
    }
    /// Clique-derivation cap for root probing (default 0 = off).
    ///
    /// Flag: `--root-probe-clique-cap <n>`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_root_probe_clique_cap(mut self, value: usize) -> Self {
        self.root_probe_clique_cap = Some(value);
        self
    }
    /// Cuts admitted per node separation batch.
    ///
    /// Flag: `--node-cut-batch <n>`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_node_cut_batch(mut self, value: usize) -> Self {
        self.node_cut_batch = Some(value);
        self
    }
    /// Minimum age before a node cut may be evicted.
    ///
    /// Flag: `--node-cut-age <n>`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_node_cut_age(mut self, value: usize) -> Self {
        self.node_cut_age = Some(value);
        self
    }
    /// Sub-solves per market-split dive visit.
    ///
    /// Flag: `--ms-dive-steps <n>`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_ms_dive_steps(mut self, value: usize) -> Self {
        self.ms_dive_steps = Some(value);
        self
    }
    /// Basis-row ceiling for GMI tableau assembly. Its own doc calls it a KILL SWITCH and says `=600` restores the pre-2026-08-01 behaviour — which nothing could do.
    ///
    /// Flag: `--gmi-max-rows <n>`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_gmi_max_rows(mut self, value: usize) -> Self {
        self.gmi_max_rows = Some(value);
        self
    }
    /// Iteration budget for the chain-shape promotion probe; `0` disables it.
    ///
    /// Flag: `--chain-probe <n>`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_chain_probe(mut self, value: usize) -> Self {
        self.chain_probe = Some(value);
        self
    }
    /// Bump-size floor below which `refactorize` keeps the PFI segment.
    ///
    /// Flag: `--bump-lu-min <n>`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_bump_lu_min(mut self, value: usize) -> Self {
        self.bump_lu_min = Some(value);
        self
    }
    /// Eta-rebuild count that promotes a cold LP to the LU engine.
    ///
    /// Flag: `--cold-lu-eta-rebuilds <n>`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_cold_lu_eta_rebuilds(mut self, value: usize) -> Self {
        self.cold_lu_eta_rebuilds = Some(value);
        self
    }
    /// Row ceiling for adopting the Forrest-Tomlin update. Its doc says the gate was made 'measurable' — it was not.
    ///
    /// Flag: `--adopt-ft-max-rows <n>`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_adopt_ft_max_rows(mut self, value: usize) -> Self {
        self.adopt_ft_max_rows = Some(value);
        self
    }
    /// Refactorization interval override (otherwise size-dependent).
    ///
    /// Flag: `--refactor-every <n>`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_refactor_every(mut self, value: usize) -> Self {
        self.refactor_every = Some(value);
        self
    }
    /// Multiplier setting the eta-file length cap before a rebuild.
    ///
    /// Flag: `--eta-cap-mult <n>`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_eta_cap_mult(mut self, value: usize) -> Self {
        self.eta_cap_mult = Some(value);
        self
    }
    /// Nonzero ceiling on LU factor fill before the factorization bails.
    ///
    /// Flag: `--lu-max-fill-nnz <n>`. Carrier added by the reader-without-writer census.
    #[must_use]
    pub fn with_lu_max_fill_nnz(mut self, value: usize) -> Self {
        self.lu_max_fill_nnz = Some(value);
        self
    }
    /// Bound margin within which a node qualifies for node-GMI separation.
    ///
    /// Flag: `--node-gmi-margin <x>`. Carrier added by the reader-without-writer census.
    ///
    /// # Errors
    ///
    /// [`EngineConfigError`] unless `value` is finite and in `[0, 1e15]` — the
    /// domain [`Setting::Real`] itself admits, so the builder cannot accept a
    /// value the accessor would then discard.
    pub fn with_node_gmi_margin(mut self, value: f64) -> Result<Self, EngineConfigError> {
        self.node_gmi_margin = Some(checked(Knob::NodeGmiMargin, value, 0.0, MAX_KNOB_SECS)?);
        Ok(self)
    }
    /// Per-probe wall slice for terminal-salvage dives, in seconds.
    ///
    /// Flag: `--dive-probe-secs <x>`. Carrier added by the reader-without-writer census.
    ///
    /// # Errors
    ///
    /// [`EngineConfigError`] unless `value` is finite and in `[0, 1e15]` — the
    /// domain [`Setting::Real`] itself admits, so the builder cannot accept a
    /// value the accessor would then discard.
    pub fn with_dive_probe_secs(mut self, value: f64) -> Result<Self, EngineConfigError> {
        self.dive_probe_secs = Some(checked(Knob::DiveProbeSecs, value, 0.0, MAX_KNOB_SECS)?);
        Ok(self)
    }
    /// Reduced-cost window for the RENS column release.
    ///
    /// Flag: `--rens-window <x>`. Carrier added by the reader-without-writer census.
    ///
    /// # Errors
    ///
    /// [`EngineConfigError`] unless `value` is finite and in `[0, 1e15]` — the
    /// domain [`Setting::Real`] itself admits, so the builder cannot accept a
    /// value the accessor would then discard.
    pub fn with_rens_window(mut self, value: f64) -> Result<Self, EngineConfigError> {
        self.rens_window = Some(checked(Knob::RensWindow, value, 0.0, MAX_KNOB_SECS)?);
        Ok(self)
    }
    /// Share of the remaining budget handed to root implication probing.
    ///
    /// Flag: `--root-probe-share <x>`. Carrier added by the reader-without-writer census.
    ///
    /// # Errors
    ///
    /// [`EngineConfigError`] unless `value` is finite and in `[0, 1e15]` — the
    /// domain [`Setting::Real`] itself admits, so the builder cannot accept a
    /// value the accessor would then discard.
    pub fn with_root_probe_share(mut self, value: f64) -> Result<Self, EngineConfigError> {
        self.root_probe_share = Some(checked(Knob::RootProbeShare, value, 0.0, MAX_KNOB_SECS)?);
        Ok(self)
    }
    /// Radius of the CDCL ball propagation search run once before the ladder.
    ///
    /// Flag: `--prop-first <x>`. Carrier added by the reader-without-writer census.
    ///
    /// # Errors
    ///
    /// [`EngineConfigError`] unless `value` is finite and in `[0, 1e15]` — the
    /// domain [`Setting::Real`] itself admits, so the builder cannot accept a
    /// value the accessor would then discard.
    pub fn with_prop_first(mut self, value: f64) -> Result<Self, EngineConfigError> {
        self.prop_first = Some(checked(Knob::PropFirst, value, 0.0, MAX_KNOB_SECS)?);
        Ok(self)
    }
    /// Lower the census-repaired carriers into the knob profile.
    ///
    /// One table rather than a hundred `if let` arms: the list is mechanical,
    /// and a table is what `tests/knob_census.rs` reads as evidence that each
    /// knob has a writer.
    pub(super) fn extend_census_profile(&self, mut p: Profile) -> Profile {
        for (knob, value) in [
            (Knob::SingletonSub, self.singleton_sub.map(Setting::Flag)),
            (Knob::NodeCutEager, self.node_cut_eager.map(Setting::Flag)),
            (Knob::AmoMultiway, self.amo_multiway.map(Setting::Flag)),
            (Knob::NodeRc, self.node_rc.map(Setting::Flag)),
            (
                Knob::NoRcCapGuard,
                self.rc_cap_guard.map(|v| Setting::Flag(!v)),
            ),
            (Knob::TriCrashAll, self.tri_crash_all.map(Setting::Flag)),
            (Knob::SymBranch, self.sym_branch.map(Setting::Flag)),
            (Knob::StabOrbit, self.stab_orbit.map(Setting::Flag)),
            (Knob::OrbitopeDyn, self.orbitope_dyn.map(Setting::Flag)),
            (
                Knob::NoTreeFloor,
                self.tree_floor.map(|v| Setting::Flag(!v)),
            ),
            (
                Knob::NoTreeBoundOutcome,
                self.tree_bound_outcome.map(|v| Setting::Flag(!v)),
            ),
            (
                Knob::NoRootFloor,
                self.root_floor.map(|v| Setting::Flag(!v)),
            ),
            (Knob::CoverMinimal, self.cover_minimal.map(Setting::Flag)),
            (Knob::GubClique, self.gub_clique.map(Setting::Flag)),
            (Knob::GmiCutTrace, self.gmi_cut_trace.map(Setting::Flag)),
            (Knob::CondTighten, self.cond_tighten.map(Setting::Flag)),
            (Knob::ModK, self.mod_k.map(Setting::Flag)),
            (Knob::KnapDbg, self.knap_dbg.map(Setting::Flag)),
            (Knob::ColdDualAll, self.cold_dual_all.map(Setting::Flag)),
            (Knob::CutWarm, self.cut_warm.map(Setting::Flag)),
            (Knob::Rlt, self.rlt.map(Setting::Flag)),
            (
                Knob::DiveCommitStopped,
                self.dive_commit_stopped.map(Setting::Flag),
            ),
            (Knob::NoRootWarm, self.root_warm.map(|v| Setting::Flag(!v))),
            (
                Knob::OrbitopeBranch,
                self.orbitope_branch.map(Setting::Flag),
            ),
            (Knob::OrbitopeIlv, self.orbitope_ilv.map(Setting::Flag)),
            (
                Knob::OrbitopeBranchDyn,
                self.orbitope_branch_dyn.map(Setting::Flag),
            ),
            (Knob::NodeCutLocal, self.node_cut_local.map(Setting::Flag)),
            (
                Knob::NoCondScout,
                self.cond_scout.map(|v| Setting::Flag(!v)),
            ),
            (Knob::HybridPbLp, self.hybrid_pb_lp.map(Setting::Flag)),
            (Knob::Attrib, self.attrib.map(Setting::Flag)),
            (Knob::Acensus, self.acensus.map(Setting::Flag)),
            (Knob::HybridTerm, self.hybrid_term.map(Setting::Flag)),
            (
                Knob::RootProbeNoLpRank,
                self.root_probe_lp_rank.map(|v| Setting::Flag(!v)),
            ),
            (Knob::MsDive, self.ms_dive.map(Setting::Flag)),
            (Knob::Mas74Plunge, self.mas74_plunge.map(Setting::Flag)),
            (Knob::RelaxLift, self.relax_lift.map(Setting::Flag)),
            (Knob::Devex, self.force_devex.map(Setting::Flag)),
            (Knob::BumpBtf, self.bump_btf.map(Setting::Flag)),
            (Knob::NodeCutSlots, self.node_cut_slots.map(Setting::Count)),
            (Knob::NodeCutEvery, self.node_cut_every.map(Setting::Count)),
            (Knob::NodeGmi, self.node_gmi.map(Setting::Count)),
            (Knob::NodeGmiEvery, self.node_gmi_every.map(Setting::Count)),
            (Knob::Scale, self.scale.map(Setting::Count)),
            (Knob::CutTopk, self.cut_topk.map(Setting::Count)),
            (Knob::SbProbeIters, self.sb_probe_iters.map(Setting::Count)),
            (Knob::RootProbeCap, self.root_probe_cap.map(Setting::Count)),
            (
                Knob::RootProbeCliqueCap,
                self.root_probe_clique_cap.map(Setting::Count),
            ),
            (Knob::NodeCutBatch, self.node_cut_batch.map(Setting::Count)),
            (Knob::NodeCutAge, self.node_cut_age.map(Setting::Count)),
            (Knob::MsDiveSteps, self.ms_dive_steps.map(Setting::Count)),
            (Knob::GmiMaxRows, self.gmi_max_rows.map(Setting::Count)),
            (Knob::ChainProbe, self.chain_probe.map(Setting::Count)),
            (Knob::BumpLuMin, self.bump_lu_min.map(Setting::Count)),
            (
                Knob::ColdLuEtaRebuilds,
                self.cold_lu_eta_rebuilds.map(Setting::Count),
            ),
            (
                Knob::AdoptFtMaxRows,
                self.adopt_ft_max_rows.map(Setting::Count),
            ),
            (Knob::RefactorEvery, self.refactor_every.map(Setting::Count)),
            (Knob::EtaCapMult, self.eta_cap_mult.map(Setting::Count)),
            (Knob::LuMaxFillNnz, self.lu_max_fill_nnz.map(Setting::Count)),
            (Knob::NodeGmiMargin, self.node_gmi_margin.map(Setting::Real)),
            (Knob::DiveProbeSecs, self.dive_probe_secs.map(Setting::Real)),
            (Knob::RensWindow, self.rens_window.map(Setting::Real)),
            (
                Knob::RootProbeShare,
                self.root_probe_share.map(Setting::Real),
            ),
            (Knob::PropFirst, self.prop_first.map(Setting::Real)),
        ] {
            if let Some(value) = value {
                p = p.with(knob, value);
            }
        }
        p
    }
}
