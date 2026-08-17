// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

pub(super) fn assert_census_matches_survey(total: usize, dead: usize) {
    // 205 -> 184 (2026-08-14): B29 — the twenty-one default-on kill switches
    // moved to typed `tune::Knob` carriers (env-less; `--no-*` /
    // `--dual-bypass-mode` / `--eager-perturb-mode` on the ay-milp CLI,
    // builders on `EngineEconomics`, `with_structure_routing` on `SolveOpts`).
    // 184 -> 181 (2026-08-14): B29 tail — the concurrent-session arrivals
    // MIR_KNAP/NO_MIR_KNAP (-> `Knob::NoMirKnap`, `--[no-]mir-knap`) and
    // DIVE_BACKTRACKS (env override folded into its named constant) retired
    // on arrival; ATTRIB and SEP_SCREEN_AUDIT stay as Diagnostic reads.
    // 181 -> 170 (2026-08-15): B37 — the eleven auto-decide overrides moved
    // to env-less tune::Knob carriers (the engine already decides; the
    // forces ride --bb-gate/--child-order/--cuts-per-round/--cut-eff-floor/
    // --ft-spike/--[no-]gub-sb/--[no-]ng-box/--ng-branch-pct/
    // --[no-]node-prop/--[no-]plunge/--[no-]sb-sustain).
    // 170 -> 149 (2026-08-15): B38 — the twenty-one knob env spellings are
    // retired and the tune env snapshot layer with them: knobs resolve
    // caller > policy > compiled default only, the spellings live on as CLI
    // flags on the shared engine_cli (which the mps_solve harness example
    // and both measurement scripts now use).
    // 149 -> 139 (2026-08-15): B39a — the ten clean keep-override singles
    // moved to env-less knobs (--sym-branch-band, --rins, --dualfix-all,
    // --implied-bound, --lifted-cover, --lnp-budget, --lattice-bkz-beta,
    // --dual-perturb, --cert-grace-secs, --anchor-first-refusal-ms).
    // 139 -> 133 (2026-08-15): B39b — the six in-crate test-steered names
    // (--rins-every, --rins-drycap, --pump-share, --setpart-share,
    // --no-parity, --no-margin-reframe) moved to caller-layer knobs; their
    // ScopedEnvVar/env-dict steerings ride activate_caller / per-solve
    // engine profiles.
    // 133 -> 131 (2026-08-15): B39b tail — AY_MILP_SYM (--sym-mode
    // orbital|rows|off) and AY_MILP_HEUR_SHARE (--heur-share) complete the
    // in-crate test-steered eight; the symmetry preserve-the-optimum test
    // drives per-arm engine profiles.
    // 131 -> 124 (2026-08-15): B39c — the seven measurement-script axes
    // (--sb-rel/--sb-cands/--sb-total, --no-presolve[-scout], --vsids,
    // --root-probe-all) moved to caller-layer knobs; joint_search's SB and
    // presolve coordinates removed with the fail-fast guard extended, the
    // portfolio probe/vsids arms pass CLI args.
    // 124 -> 116 (2026-08-15): B40 — the eight diagnostics (--sepstat,
    // --lp-stats, --step-trace, --bump-diag, --bumpdiff-lanes,
    // --diag-plain-cold, --dump-vertex; --iter-ledger on the mps_solve
    // example) moved to caller-layer knobs / the example's parsed flags.
    // 116 -> 112 (2026-08-15): B40b — the example-only harness knobs
    // (--lu, --prefix-cols, --obbt-cols on milp_profile; --smt-lane on
    // milp_speed AND the session lane force via Knob::SmtLane) moved to
    // parsed flags / the caller layer.
    // 112 -> 106 (2026-08-15): B46 — the six never-set diagnostic streams
    // (TRACE, MS_DIVE_TRACE, COEF_TIGHTEN_DEBUG, SYM_DEBUG, SHAPE_CENSUS,
    // SEP_SCREEN_AUDIT) became engine-CLI switches on MilpDebugFlags.
    // 106 -> 105 (2026-08-15): B48 — MAX_NODES became the typed MaxNodes
    // knob (with_max_nodes / --max-nodes), tests steer via engine profiles.
    // 105 -> 97 (2026-08-16): B49 — the eight test-steered opt-in arms
    // (STRUCT_ELIM, NO_BOUND_COVER, PUMP_ITER_MULT, NO_PUMP_ITER_CAP,
    // NG_UP, CUT_SHADOW, CHAIN_AGG, AUTO_MARGIN) became typed knobs;
    // tests steer via engine profiles / caller overlays.
    // 97 -> 91 (2026-08-16): B50 — the six conflict-learning levers
    // (IMPL, IMPL_ARM, PROP_CONFLICT, LB_CONFLICT, LB_ARM, LB_STRICT)
    // became typed knobs on EngineEconomics.
    // 91 -> 81 (2026-08-16): B51 — the node-cut/GMI/RC cluster + singleton
    // substitution + AMO multiway became typed knobs; the fossilized
    // "--node-cuts" mangled env read died with the presence gate.
    // 81 -> 74 (2026-08-16): B52 — sym-branch, stab-orbit, scale,
    // orbitope-dyn, and the three floor/report disables became typed knobs.
    // 74 -> 72 (2026-08-16): B53 — cover-minimal + gub-clique, the last
    // two test-set names, became typed knobs. The milp test-set env class
    // is now EMPTY.
    // 72 -> 56 (2026-08-16): B62 — sixteen ledgered presence-single arms
    // arms became typed knobs (orbitope branching family, cut arms, cold
    // dual, warm starts, diagnostics).
    // 56 -> 55 (2026-08-16): B64 — LNP_PROBE became the --lnp-probe
    // engine-CLI path carrier on MilpDebugFlags.
    // 55 -> 53 (2026-08-16): B66 — root-closure-presolve + tri-crash-all
    // became typed knobs.
    // 53 -> 52 (2026-08-16): B70 — CHECK_SOL became the --check-sol
    // engine-CLI value flag on the mps_solve example.
    // 52 -> 19 (2026-08-16): B71 — the entire remaining value/experiment
    // block (33 names: probes, caps, LU levers, dives, hybrid arms,
    // censuses) became typed knobs; ay-milp src now has ZERO env reads
    // outside the ledger fixtures.
    assert_eq!(total, 19, "AY_* name count moved");
    assert_eq!(dead, 11, "dead-knob count moved");
}
