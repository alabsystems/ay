// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tuning-knob identities and their stable carrier variants.

/// A tunable the engine may decide for itself.
///
/// Only *performance-relevant* settings belong here. The great majority of the
/// crate's environment variables are diagnostics (the --trace stream,
/// `AY_MILP_*_DEBUG`) or A/B kill switches that exist so a measurement can
/// disable one mechanism; neither is something the engine should decide, and
/// neither appears in this enum.
///
/// The second block is different in kind: those twelve are the knobs an
/// embedding *consumer* configures per solve. They are here because
/// [`crate::EngineEconomics`] needs a typed carrier for them and this is the
/// crate's one table mapping a setting to its historical environment spelling;
/// giving them a second, parallel table is how a kill switch and its typed
/// setter come to disagree.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Knob {
    /// Full GMI/MIR separation rounds at the root.
    GmiRounds,
    /// Cuts retained per round at the root (node budget is separate).
    RootCutsPerRound,
    /// Run implication probing at the root.
    RootProbe,
    /// Depth-first node selection.
    Dfs,
    /// Separate cuts at nodes below the root.
    NodeCuts,
    /// Dive toward a leaf after branching, to buy an incumbent.
    Plunge,

    // The twelve `crates/ny-mip/src/ay_lib.rs` pins today, per
    // the development design notes §M1. Negative senses
    // (`No*`) are kept exactly as the environment spells them, because the
    // accessor convention is per *variable*, not per concept: inverting one
    // here to read positively would flip what an operator's existing
    // `--no-cuts` means. The public builder is positive-sense
    // (`with_cuts(false)`) and does the one inversion, in one place.
    /// Disable the market-split lattice detector (`lattice::try_prove`).
    NoLattice,
    /// Disable the flip-LNS saturation stop.
    NoSatStop,
    /// Saturation-stop dry-spell floor, in seconds.
    SatStopSecs,
    /// Saturation-stop multiplier on the largest observed improvement gap.
    SatStopMult,
    /// Disable the tall-degenerate bloom-cap relaxation.
    NoBloomRelax,
    /// Absolute cap on the flip-LNS window for `tall_lu` models, in seconds.
    FlipCapSecs,
    /// Flip-LNS share of the remaining budget. Setting it at all also opts out
    /// of the absolute cap — see the call site at `bab.rs:19251`.
    FlipShare,
    /// Install an LU engine in the pooled `WarmSolver`.
    WarmLu,
    /// Share of the remaining budget handed to bound-propagation presolve.
    PresolveShare,
    /// Disable root cut separation.
    NoCuts,
    /// Feasibility-pump restart allowance (`0` skips the pump).
    PumpRestarts,
    /// Cap on committed pins in the terminal-salvage dive.
    DiveMaxPins,

    // The REDUCTION knobs. These are not search economics: three of them gate
    // transformations that change the model a verdict is proved against, and a
    // consumer whose admission requires certificates needs to reach them by
    // value, not by exporting a variable. `ny` cannot export one at all -- its
    // policy forbids writing `AY_MILP_*` -- so before these existed it had no
    // in-policy way to quarantine a reduction. Same negative spelling
    // convention as the block above: the variable keeps its name, the public
    // builder is positive-sense and does the single inversion.
    /// Disable dual fixing by lock counting (`dualfix::dual_fix`). A WLOG
    /// reduction: it preserves the ANSWER, not the feasible set.
    NoDualfix,
    /// Disable the AHL kernel reformulation (`lattice::reformulate_kernel`).
    NoKernelReform,
    /// Disable decoupling root reductions from certificate capture, restoring
    /// the prior `tree_cert_leaves == 0` gating byte-identically.
    NoCertDecouple,
    /// Disable the zero-objective feasibility conflict class (nogood
    /// propagation, nogood-guided branching, VSIDS).
    NoFeasConflict,
    /// Disable the cold-root LU band, restoring the historical eta-file cold
    /// root byte-for-byte.
    NoColdLu,

    // B11 knobs: migrated from never-set `AY_MILP_*` env reads. These have NO
    // environment spelling (`env()` returns `None`) — nothing ever set the
    // variables, so the carrier is caller > policy > compiled default, and the
    // env layer is not a party to the lookup. Negative senses kept per the
    // convention above; the public builders are positive-sense.
    /// Disable variable-upper-bound extraction for node/root cut separation.
    NoVub,
    /// Disable the narrowed MIR general-integer gate (restores all-integral).
    NoMirGenint,
    /// Disable the separation screen (exact deltas for every candidate).
    NoSepScreen,
    /// Disable the Forrest–Tomlin fast (bounds-check-elided) update path.
    NoFtFast,
    /// Disable the dense `ftran` fast path.
    NoFtranFast,
    /// Disable the sparse `ftran_nz` fast path.
    NoFtranNzFast,
    /// Disable the O(m) counting sort of sparse-solve reach sets.
    NoCountsort,
    /// Disable presolve coefficient tightening.
    NoCoefTighten,
    /// Disable static orbitope assembly (keep the per-branch orbit walk).
    NoOrbitope,
    /// Forrest–Tomlin growth tolerance override (refactorization trigger).
    FtGrowthTol,

    // B12 dual-simplex lanes: no env spelling; caller > policy > compiled default.
    /// Dual-walk anatomy tracing (diagnostic; hot loop pays one bool per walk).
    DualAnatomy,
    /// Pivot count after which the walk re-verifies the basis factorization.
    VerifyAfter,
    /// Disable the fused one-pass ratio test (restores the two-pass A/B baseline).
    NoFusedRt,
    /// Disable the incremental ratio-test eligibility bitmask.
    NoRtKind,
    /// Per-iteration ratio-test profiler (diagnostic).
    IterProfile,
    /// Disable the bare-u64 ratio-test compare key.
    NoRtBitsKey,
    /// Disable the wide set-partition bloom-cap divergence-guard lift.
    NoWideBloom,
    /// Disable cross-solve eta reuse (restores per-warm-solve rebuilds).
    NoEtaReuse,
    /// Disable devex pricing.
    NoDevex,
    /// Disable the cold dual-simplex start on wide-and-tall LPs.
    NoColdDual,
    /// Disable the triangular equality crash on big cold LPs.
    NoTriCrash,
    /// Chained-devex mode: 0 | 1 | 2 (the measured default).
    ChainDevex,
    /// Disable the objective-cutoff early stop in the warm dual walk.
    NoCutoff,
    /// Disable the warm-solve LU engine on wide-tall plain_cold instances.
    NoNodeLu,
    /// Disable the tall LU gate.
    NoTallLu,
    /// Disable cold dual-simplex on tall covering LPs (`m > n`).
    NoTallColdDual,
    /// Disable the dual churn band.
    NoDualChurnBand,
    /// Override the dual bloom cap.
    DualBloomCap,

    // B13: branch-and-bound knobs (cut families, LNS, branching); no env spellings.
    /// Disable the aggregated flow-cover side pool.
    NoFlowcoverAgg,
    /// Disable the general-integer GMI extension rounds.
    NoGiExt,
    /// Disable the small-symmetric-bottleneck GMI extension.
    NoBottleneckExt,
    /// Disable clique separation.
    NoClique,
    /// Disable lifted odd-hole separation.
    NoOddCycle,
    /// Disable cover-bought extended separation rounds.
    NoCoverExt,
    /// Disable flow-cover separation (both call sites).
    NoFlowcover,
    /// Disable cut-coefficient snapping.
    NoSnap,
    /// Disable the set-partitioning LNS.
    NoSplns,
    /// Disable the market-share walk.
    NoMsWalk,
    /// Disable the sweep/prove wall split on routing models.
    NoSweepProve,
    /// Disable the RINS cadence rescue.
    NoRinsRescue,
    /// Disable MILP symmetry handling.
    NoSym,
    /// Pin best-bound node selection for all sub-MIP arms (default: DFS below level 3).
    SubmipBb,
    /// Force zero-half separation on (beyond the pure-set-partitioning auto-arm).
    ZeroHalf,
    /// Force lifted odd-hole separation on (beyond the wide-set-partition auto-arm).
    OddCycle,
    /// Flip-LNS reach instrumentation (trace-only diagnostic).
    FlipReach,
    /// Bound-propagation sweep cap.
    PropSweeps,
    /// Bound-propagation queue cap.
    PropQueue,
    /// Set-partitioning LNS exposed-region cap.
    SplnsExposed,
    /// Set-partitioning LNS node budget.
    SplnsBudget,
    /// Set-partitioning LNS stall window, in seconds.
    SplnsStall,
    /// Market-share walk move budget.
    MsWalkMoves,
    /// Print the frontier peek bound every N nodes (measurement).
    GubMeasEvery,
    /// Deterministic hashed cost perturbation magnitude (diagnostic).
    DiagCostPerturb,
    /// Flow-cost branching mode: 0..=3 (the measured default is 3-gated auto).
    FcMode,
    /// Flip-aggregate solve arm: 0 auto (density test), 1 sparse, 2 dense.
    FlipSolve,

    // B29 knobs: the remaining default-on `AY_MILP_*` kill switches, moved to
    // typed carriers with NO environment spelling (caller > compiled default;
    // the env layer is not a party). Negative senses per the convention above.
    /// Disable GUB/SOS1 branching arming.
    NoGubBranch,
    /// Disable duplicate-column presolve merging.
    NoDedupCols,
    /// Disable binary equivalence/complement substitution.
    NoBinaryComplementSub,
    /// Disable coldest-first no-good box replacement (restore oldest-first).
    NoLbAct,
    /// Disable depth-first routing for the pure general-integer shape.
    NoGiDfs,
    /// Disable objective-cutoff-row propagation.
    NoImplCut,
    /// Disable the mined-implication table pass.
    NoImplTab,
    /// Disable the knapsack dry-ball narrow redirect.
    NoKnapRedirect,
    /// Disable the terminal-dive poison-column deferral.
    NoDiveSkip,
    /// Disable fused clone-free exact cut/LU accumulation (restore the
    /// literal clone-then-multiply form for byte-identity A/Bs).
    NoCutFma,
    /// Disable odd-hole cut lifting (bare holes only).
    NoOddLift,
    /// Disable strong-CG separation.
    NoStrongcg,
    /// Rebuild the dense GMI basis (opt-in; restores the pre-sparse path).
    DenseGmiLu,
    /// Disable the chain-shape structural class gate.
    NoChainShape,
    /// Disable chain-verdict-driven refactorize peel preorder.
    NoChainPreorder,
    /// Disable the BUMP-LU base factor inside refactorize.
    NoBumpLu,
    /// Dual-bypass mode: 0 never, 1 adaptive (default), 2 force.
    DualBypassMode,
    /// Eager-perturb mode: 0 off, 1 armed-on-stall (default), 2 all walks.
    EagerPerturbMode,
    /// PRIMAL Harris two-pass ratio test: 0 off (the default, and the
    /// byte-identical single-pass path), 1 two-pass largest-pivot selection,
    /// 2 two-pass plus the bounded positive step floor (EXPAND-style).
    HarrisRt,
    /// Disable the knapsack-form complementation search in MIR/strong-CG row
    /// preparation (`with_mir_knap(true)` forces it beyond a moved default).
    NoMirKnap,

    // B37 knobs: overrides over decisions the engine already makes
    // structurally (env-less; caller > compiled auto decision).
    /// Opt-in bound-branch gate (measured net-negative on its own gate;
    /// engages only on explicit request).
    BbGate,
    /// Child-order force: 0 away, 1 up, 2 dn, 3 lp; unset = shape auto.
    ChildOrderMode,
    /// Root cuts-per-round force; unset = the shape-gated default.
    CutsPerRound,
    /// Root cut-efficacy floor force; unset = aspect-ratio auto (0 disables).
    CutEffFloor,
    /// Forrest-Tomlin spike arm: 1 dense, 2 sparse; unset = measured auto.
    FtSpikeArm,
    /// Strong GUB branching force; unset = on iff wide.
    GubSb,
    /// Box no-good widening force; unset = structural gate.
    NgBox,
    /// No-good branching band, in percent; unset = 25 iff ng_up armed.
    NgBranchPct,
    /// Branch-row propagation force; unset = mixed-lever default.
    NodeProp,
    /// Strong-branching sustain force; unset = mixed-lever default.
    SbSustain,

    // B39 knobs: the clean keep-override singles (env-less; caller >
    // compiled default).
    /// Symmetry-branch band force, in percent of the orbit budget.
    SymBranchBand,
    /// RINS arming force (unset = the structural auto decision).
    Rins,
    /// Offer dual fixing on every model shape (opt-in widening).
    DualfixAll,
    /// Implied-bound separator arming (opt-in).
    ImpliedBound,
    /// Lifted-cover separator arming (opt-in).
    LiftedCover,
    /// Lift-and-project budget force; unset = the shipped default.
    LnpBudget,
    /// Lattice BKZ beta override; unset = the size-derived beta.
    LatticeBkzBeta,
    /// Dual-perturbation mode force.
    DualPerturb,
    /// Certificate grace budget force, in seconds (`0` = uncapped).
    CertGraceSecs,
    /// Anchor first-refusal window force, in milliseconds.
    AnchorFirstRefusalMs,
    // B39b knobs.
    /// RINS cadence force, in nodes.
    RinsEvery,
    /// RINS dry-spell cap force (`0` = off).
    RinsDrycap,
    /// Feasibility-pump share pin (bypasses the work cap).
    PumpShare,
    /// Set-partition constructor share pin (restores the pure fraction).
    SetpartShare,
    /// Disable the enlight-parity exact route.
    NoParity,
    /// Disable margin reframing module-wide.
    NoMarginReframe,
    /// Symmetry handling mode: 0 orbital (default), 1 rows, 2 off.
    SymMode,
    /// Root heuristic share pin (unset = the shape-dependent default).
    HeurShare,
    // B39c knobs (the measurement-script axes).
    /// Strong-branching reliability threshold force.
    SbRel,
    /// Strong-branching candidate count force.
    SbCands,
    /// Strong-branching total probe budget pin.
    SbTotal,
    /// Skip presolve entirely.
    NoPresolve,
    /// Skip the presolve scout plan.
    NoPresolveScout,
    /// VSIDS branching force (unset = the feasibility-class gate).
    Vsids,
    /// Probe every binary at the root (opt-in widening).
    RootProbeAll,
    // B40 knobs: diagnostics (opt-in instruments; never engine decisions).
    /// Separation-statistics census dump.
    Sepstat,
    /// Per-solve LP statistics line.
    LpStats,
    /// Simplex step trace, first N steps.
    StepTraceN,
    /// BUMP-LU factor diagnostics.
    BumpDiag,
    /// bumpdiff lane pair, encoded a*10+b (lanes 0..=2, a != b).
    BumpdiffLanes,
    /// Plain-cold LP diagnostic arm.
    DiagPlainCold,
    /// Root vertex dump.
    DumpVertex,
    /// Force the ay-dpll SMT lowering lane instead of native B&B (A/B).
    SmtLane,
    /// MEASUREMENT-ONLY node cap: stop after N nodes with a valid Feasible or
    /// dual-bound outcome. `Some(0)` stops before the first node.
    MaxNodes,

    // B49 knobs: the test-steered opt-in arms (were test-only-set env vars;
    // same contract — no env spelling, caller > policy > compiled default).
    /// Opt in to the structure-attack elimination arm.
    StructElim,
    /// Disable the dual-bound cover pass (cover is ON when unset).
    NoBoundCover,
    /// Feasibility-pump iteration-cap multiplier (finite, >= 0).
    PumpIterMult,
    /// Remove the pump iteration cap entirely.
    NoPumpIterCap,
    /// Nogood upward propagation: `false` = off, `true` = force, unset =
    /// the shape-dependent auto arm.
    NgUp,
    /// Cut-shadow audit mode: 1 = binding, 2 = slack; unset = off.
    CutShadow,
    /// Opt in to MIR chain aggregation.
    ChainAgg,
    /// Opt in to automatic margin-row detection on zero-objective models.
    AutoMargin,
    /// Implication lane: `false` = off, `true` = force, unset = class auto.
    ImplLane,
    /// Implication-lane arming node override (default: the mixed-lever arm).
    ImplArm,
    /// Leaf-drought plunge cadence: `0` disables; `n` arms at node `n` and dives
    /// every `n` pops; unset uses `DROUGHT_ARM_NODES`/`DROUGHT_DIVE_EVERY`.
    DroughtDive,
    /// Propagation-conflict learning: `false` = off, `true` = force, unset =
    /// the implication/feasibility class auto.
    PropConflict,
    /// Bound-prune conflict learning: 1 = on the mixed-store class, 2 =
    /// force everywhere; unset = off.
    LbConflict,
    /// Bound-prune learning arming node override.
    LbArm,
    /// Strict bound-prune admission (default true; `false` admits unrelaxed
    /// boxes for A/B).
    LbStrict,
    /// Opt in to the singleton-substitution reduction.
    SingletonSub,
    /// Opt in to the exact implied-free equality-aggregation reduction.
    AffineAgg,
    /// Node-cut slot count override (`0` disables; setting it at all opts
    /// node cuts in).
    NodeCutSlots,
    /// Node-cut cadence floor override (> 0).
    NodeCutEvery,
    /// Eager node-cut separation.
    NodeCutEager,
    /// Exact-AMO multiway branching arm.
    AmoMultiway,
    /// Node-GMI rounds per visit (`0` = off).
    NodeGmi,
    /// Node-GMI cadence (> 0; default 500).
    NodeGmiEvery,
    /// Node-GMI owner margin (default 1.0).
    NodeGmiMargin,
    /// Node reduced-cost fixing arm.
    NodeRc,
    /// Disarm the reduced-cost cap guard (restores unguarded caps).
    NoRcCapGuard,
    /// Root closure-presolve subject arm.
    RootClosurePresolve,
    /// Force the triangular crash on all cold LPs.
    TriCrashAll,
    /// Symmetry-aware branching (default on; `false` disables).
    SymBranch,
    /// Orbit-stabilizer chain refinement arm.
    StabOrbit,
    /// LP equilibration mode: 1 = force, 2 = auto; unset = off.
    Scale,
    /// Dynamic orbitope branch-history arm.
    OrbitopeDyn,
    /// Disable the tree dual-bound floor.
    NoTreeFloor,
    /// Disable the tree-bound outcome report.
    NoTreeBoundOutcome,
    /// Disable the root dual-bound floor.
    NoRootFloor,
    /// Minimal-cover strengthening arm.
    CoverMinimal,
    /// GUB clique branching arm.
    GubClique,
    /// GMI cut trace (diagnostic).
    GmiCutTrace,
    /// Conditional-tightening presolve arm.
    CondTighten,
    /// Mod-k cut separation arm.
    ModK,
    /// Knapsack-cover diagnostics.
    KnapDbg,
    /// Root MIR aggregation arm.
    MirAggRoot,
    // RETIRED: `LnpProbePresolve`. Its only reader lived inside a `#[cfg(test)]`
    // probe in `cuts.rs` and it had no writer on any surface, so no build could
    // set it and the branch it guarded was unreachable. Deleting the variant is
    // behaviour-preserving; see the note at the former reader.
    /// Cold dual simplex on ALL LPs.
    ColdDualAll,
    /// Warm-started cut rounds arm.
    CutWarm,
    /// RLT separation arm.
    Rlt,
    /// Tableau-row MIR arm.
    TableauMir,
    /// Commit stopped dives.
    DiveCommitStopped,
    /// Disable root warm start.
    NoRootWarm,
    /// Orbitope-aware branching arm.
    OrbitopeBranch,
    /// Orbitope interleaving arm.
    OrbitopeIlv,
    /// Dynamic orbitope branching arm.
    OrbitopeBranchDyn,
    /// Local node cuts arm.
    NodeCutLocal,
    /// Disable the conditional-tightening scout.
    NoCondScout,
    /// Disable the float lane (exact only).
    NoFloat,
    /// Hybrid PB-LP certified decision arm.
    HybridPbLp,
    /// LP call-site attribution census (diagnostic).
    Attrib,
    /// Allocation census (diagnostic).
    Acensus,
    /// Cuts kept per round (0 = unlimited).
    CutTopk,
    /// Hybrid branching term arm.
    HybridTerm,
    /// Dive probe budget seconds.
    DiveProbeSecs,
    /// Strong-branch probe dual iterations.
    SbProbeIters,
    /// RENS release window (>= 0).
    RensWindow,
    /// Root probe cap.
    RootProbeCap,
    /// Root probe clique cap.
    RootProbeCliqueCap,
    /// Disable LP-rank probe ordering.
    RootProbeNoLpRank,
    /// Root probe deadline share.
    RootProbeShare,
    /// Node cuts per visit (> 0).
    NodeCutBatch,
    /// Node cut minimum age.
    NodeCutAge,
    /// External dual bound as a cutoff (objective frame).
    DualCutoff,
    /// Market-split dive arm.
    MsDive,
    /// mas74-class plunge (default on; false disables).
    Mas74Plunge,
    /// Market-split dive per-solve steps.
    MsDiveSteps,
    /// Ball-propagation-first radius.
    PropFirst,
    /// GMI basis-row cap.
    GmiMaxRows,
    /// Chain-shape probe iterations.
    ChainProbe,
    /// Bump-size floor for LU refactorization.
    BumpLuMin,
    /// Cold-LU eta rebuild count.
    ColdLuEtaRebuilds,
    /// FT adoption tall-row cap.
    AdoptFtMaxRows,
    /// Force refactorization cadence.
    RefactorEvery,
    /// Eta cap multiplier.
    EtaCapMult,
    /// LU fill safety ceiling (nnz).
    LuMaxFillNnz,
    /// Relax-and-lift cover separation arm.
    RelaxLift,
    /// Force Devex pricing from iteration 0.
    Devex,
    /// Bump BTF diagnostics.
    BumpBtf,
}
