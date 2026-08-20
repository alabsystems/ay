// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Typed engine-economics CLI overrides, shared by the `ay-milp` binary and
//! the measurement-harness example drivers (B38: the harness scripts pass
//! these flags instead of the retired `AY_MILP_*` env spellings).

use crate::{EngineEconomics, SolveOpts};

type BoolBuilder = fn(EngineEconomics, bool) -> EngineEconomics;
type UsizeBuilder = fn(EngineEconomics, usize) -> EngineEconomics;
type FloatBuilder = fn(EngineEconomics, f64) -> Result<EngineEconomics, crate::EngineConfigError>;

/// Hand-rolled argument bag (this crate takes no CLI dependency): `--x v` /
/// `--x=v` for names in `value_flags`, bare `--x` switches otherwise,
/// positionals passed through.
pub struct Flags {
    pub positional: Vec<String>,
    named: Vec<(String, String)>,
    switches: Vec<String>,
}

impl Flags {
    /// Parse `args`; names listed in `value_flags` take a value.
    ///
    /// # Errors
    ///
    /// A message when a value flag is missing its value or a switch was
    /// given one.
    pub fn parse(args: &[String], value_flags: &[&str]) -> Result<Self, String> {
        let mut f = Flags {
            positional: Vec::new(),
            named: Vec::new(),
            switches: Vec::new(),
        };
        let mut i = 0;
        while i < args.len() {
            let a = &args[i];
            if let Some(name) = a.strip_prefix("--") {
                let (name, inline) = match name.split_once('=') {
                    Some((n, v)) => (n, Some(v.to_string())),
                    None => (name, None),
                };
                if value_flags.contains(&name) {
                    let v = match inline {
                        Some(v) => v,
                        None => {
                            i += 1;
                            args.get(i)
                                .ok_or_else(|| format!("--{name} needs a value"))?
                                .clone()
                        }
                    };
                    f.named.push((name.to_string(), v));
                } else {
                    if inline.is_some() {
                        return Err(format!("--{name} takes no value"));
                    }
                    f.switches.push(name.to_string());
                }
            } else {
                f.positional.push(a.clone());
            }
            i += 1;
        }
        Ok(f)
    }

    /// The last value given for `name`, if any.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&String> {
        self.named
            .iter()
            .rev()
            .find(|(n, _)| n == name)
            .map(|(_, v)| v)
    }

    /// Whether the bare switch `name` was given.
    #[must_use]
    pub fn has(&self, name: &str) -> bool {
        self.switches.iter().any(|s| s == name)
    }
}

pub const VALUE_FLAGS: &[&str] = &[
    "check-sol",
    "dual-cutoff",
    "kernel-scan-dir",
    "lnp-probe",
    "time-limit",
    "threads",
    "seed",
    "memory-budget",
    "tree-cert-leaves",
    "seed-solution",
    "require",
    "emit-cert",
    "emit-cert-max-bytes",
    "emit-witness",
    "witness-format",
    "format",
    "ft-growth-tol",
    "verify-after",
    "chain-devex",
    "dual-bloom-cap",
    "prop-sweeps",
    "prop-queue",
    "splns-exposed",
    "splns-budget",
    "splns-stall-secs",
    "ms-walk-moves",
    "gub-meas-every",
    "diag-cost-perturb",
    "fc-mode",
    "flip-solve",
    "dual-bypass-mode",
    "eager-perturb-mode",
    "cuts-per-round",
    "cut-eff-floor",
    "ng-branch-pct",
    "child-order",
    "ft-spike",
    "gmi-rounds",
    "root-cuts-per-round",
    "pump-restarts",
    "dive-max-pins",
    "flip-share",
    "presolve-share",
    "sat-stop-secs",
    "sat-stop-mult",
    "flip-cap-secs",
    "lnp-budget",
    "lattice-bkz-beta",
    "anchor-first-refusal-ms",
    "sym-branch-band",
    "rins",
    "dual-perturb",
    "cert-grace-secs",
    "rins-every",
    "rins-drycap",
    "pump-share",
    "setpart-share",
    "heur-share",
    "sym-mode",
    "sb-rel",
    "sb-cands",
    "sb-total",
    "step-trace",
    "bumpdiff-lanes",
    "drought-dive",
];

// `--no-x` carries false into a positive-sense builder; diagnostics carry true.
const BOOL_BUILDERS: &[(&str, BoolBuilder, bool)] = &[
    ("no-vub", EngineEconomics::with_vub, false),
    ("no-mir-genint", EngineEconomics::with_mir_genint, false),
    ("no-sep-screen", EngineEconomics::with_sep_screen, false),
    ("no-ft-fast", EngineEconomics::with_ft_fast, false),
    ("no-ftran-fast", EngineEconomics::with_ftran_fast, false),
    (
        "no-ftrannz-fast",
        EngineEconomics::with_ftran_nz_fast,
        false,
    ),
    ("no-countsort", EngineEconomics::with_countsort, false),
    ("no-coef-tighten", EngineEconomics::with_coef_tighten, false),
    ("no-orbitope", EngineEconomics::with_orbitope, false),
    ("no-fused-rt", EngineEconomics::with_fused_rt, false),
    ("no-rt-kind", EngineEconomics::with_rt_kind, false),
    ("no-rt-bits-key", EngineEconomics::with_rt_bits_key, false),
    ("no-wide-bloom", EngineEconomics::with_wide_bloom, false),
    ("no-eta-reuse", EngineEconomics::with_eta_reuse, false),
    ("no-devex", EngineEconomics::with_devex, false),
    ("no-cold-dual", EngineEconomics::with_cold_dual, false),
    ("no-tri-crash", EngineEconomics::with_tri_crash, false),
    ("no-cutoff", EngineEconomics::with_cutoff_stop, false),
    ("no-node-lu", EngineEconomics::with_node_lu, false),
    ("no-tall-lu", EngineEconomics::with_tall_lu, false),
    (
        "no-dual-churn-band",
        EngineEconomics::with_dual_churn_band,
        false,
    ),
    ("dual-anatomy", EngineEconomics::with_dual_anatomy, true),
    ("iter-profile", EngineEconomics::with_iter_profile, true),
    (
        "no-flowcover-agg",
        EngineEconomics::with_flowcover_agg,
        false,
    ),
    ("no-gi-ext", EngineEconomics::with_gi_ext, false),
    (
        "no-bottleneck-ext",
        EngineEconomics::with_bottleneck_ext,
        false,
    ),
    ("no-clique", EngineEconomics::with_clique, false),
    ("no-odd-cycle", EngineEconomics::with_odd_cycle, false),
    ("odd-cycle", EngineEconomics::with_odd_cycle, true),
    ("no-cover-ext", EngineEconomics::with_cover_ext, false),
    ("no-flowcover", EngineEconomics::with_flowcover, false),
    ("no-snap", EngineEconomics::with_snap, false),
    ("no-splns", EngineEconomics::with_splns, false),
    ("no-ms-walk", EngineEconomics::with_ms_walk, false),
    ("no-sweep-prove", EngineEconomics::with_sweep_prove, false),
    ("no-rins-rescue", EngineEconomics::with_rins_rescue, false),
    ("no-sym", EngineEconomics::with_sym, false),
    (
        "submip-best-bound",
        EngineEconomics::with_submip_best_bound,
        true,
    ),
    ("zero-half", EngineEconomics::with_zero_half, true),
    ("flip-reach", EngineEconomics::with_flip_reach, true),
    ("no-gub-branch", EngineEconomics::with_gub_branch, false),
    ("no-dedup-cols", EngineEconomics::with_dedup_cols, false),
    (
        "no-binary-complement-sub",
        EngineEconomics::with_binary_complement_sub,
        false,
    ),
    ("no-lb-act", EngineEconomics::with_lb_activity, false),
    ("no-gi-dfs", EngineEconomics::with_gi_dfs, false),
    ("no-impl-cut", EngineEconomics::with_impl_cut, false),
    ("no-impl-tab", EngineEconomics::with_impl_tab, false),
    (
        "no-knap-redirect",
        EngineEconomics::with_knap_redirect,
        false,
    ),
    ("no-dive-skip", EngineEconomics::with_dive_skip, false),
    ("no-cut-fma", EngineEconomics::with_cut_fma, false),
    ("no-odd-lift", EngineEconomics::with_odd_lift, false),
    ("no-strongcg", EngineEconomics::with_strongcg, false),
    ("no-mir-knap", EngineEconomics::with_mir_knap, false),
    ("mir-knap", EngineEconomics::with_mir_knap, true),
    ("bb-gate", EngineEconomics::with_bound_branch, true),
    ("no-gub-sb", EngineEconomics::with_gub_sb, false),
    ("gub-sb", EngineEconomics::with_gub_sb, true),
    ("no-ng-box", EngineEconomics::with_ng_box, false),
    ("ng-box", EngineEconomics::with_ng_box, true),
    ("no-node-prop", EngineEconomics::with_node_prop, false),
    ("node-prop", EngineEconomics::with_node_prop, true),
    ("no-sb-sustain", EngineEconomics::with_sb_sustain, false),
    ("sb-sustain", EngineEconomics::with_sb_sustain, true),
    ("no-plunge", EngineEconomics::with_plunge, false),
    ("plunge", EngineEconomics::with_plunge, true),
    ("root-probe", EngineEconomics::with_root_probe, true),
    ("no-root-probe", EngineEconomics::with_root_probe, false),
    ("dfs", EngineEconomics::with_dfs, true),
    ("no-dfs", EngineEconomics::with_dfs, false),
    ("node-cuts", EngineEconomics::with_node_cuts, true),
    ("no-node-cuts", EngineEconomics::with_node_cuts, false),
    ("no-lattice", EngineEconomics::with_lattice, false),
    ("no-sat-stop", EngineEconomics::with_saturation_stop, false),
    (
        "no-bloom-relax",
        EngineEconomics::with_bloom_cap_relaxation,
        false,
    ),
    ("warm-lu", EngineEconomics::with_warm_lu, true),
    ("no-warm-lu", EngineEconomics::with_warm_lu, false),
    ("no-cuts", EngineEconomics::with_cuts, false),
    ("no-dualfix", EngineEconomics::with_dual_fixing, false),
    (
        "no-kernel-reform",
        EngineEconomics::with_kernel_reformulation,
        false,
    ),
    (
        "no-feas-conflict",
        EngineEconomics::with_feasibility_conflict,
        false,
    ),
    ("no-cold-lu", EngineEconomics::with_cold_root_lu, false),
    ("dualfix-all", EngineEconomics::with_dualfix_all, true),
    ("implied-bound", EngineEconomics::with_implied_bound, true),
    ("lifted-cover", EngineEconomics::with_lifted_cover, true),
    ("no-parity", EngineEconomics::with_parity, false),
    ("no-presolve", EngineEconomics::with_presolve, false),
    (
        "no-presolve-scout",
        EngineEconomics::with_presolve_scout,
        false,
    ),
    ("vsids", EngineEconomics::with_vsids, true),
    ("no-vsids", EngineEconomics::with_vsids, false),
    ("root-probe-all", EngineEconomics::with_root_probe_all, true),
    ("sepstat", EngineEconomics::with_sepstat, true),
    ("lp-stats", EngineEconomics::with_lp_stats, true),
    ("bump-diag", EngineEconomics::with_bump_diag, true),
    (
        "diag-plain-cold",
        EngineEconomics::with_diag_plain_cold,
        true,
    ),
    ("dump-vertex", EngineEconomics::with_dump_vertex, true),
    ("smt-lane", EngineEconomics::with_smt_lane, true),
    (
        "no-margin-reframe",
        EngineEconomics::with_margin_reframe,
        false,
    ),
    ("dense-gmi-lu", EngineEconomics::with_dense_gmi_lu, true),
    ("no-chain-shape", EngineEconomics::with_chain_shape, false),
    (
        "no-chain-preorder",
        EngineEconomics::with_chain_preorder,
        false,
    ),
    ("no-bump-lu", EngineEconomics::with_bump_lu, false),
    ("full-pricing", EngineEconomics::with_full_pricing, true),
];

const USIZE_BUILDERS: &[(&str, UsizeBuilder)] = &[
    ("verify-after", EngineEconomics::with_verify_after),
    ("cuts-per-round", EngineEconomics::with_cuts_per_round),
    ("gmi-rounds", EngineEconomics::with_gmi_rounds),
    (
        "root-cuts-per-round",
        EngineEconomics::with_root_cuts_per_round,
    ),
    ("pump-restarts", EngineEconomics::with_pump_restarts),
    ("dive-max-pins", EngineEconomics::with_dive_max_pins),
    ("lnp-budget", EngineEconomics::with_lnp_budget),
    ("lattice-bkz-beta", EngineEconomics::with_lattice_bkz_beta),
    (
        "anchor-first-refusal-ms",
        EngineEconomics::with_anchor_first_refusal_ms,
    ),
    ("rins-every", EngineEconomics::with_rins_every),
    ("rins-drycap", EngineEconomics::with_rins_drycap),
    ("sb-rel", EngineEconomics::with_sb_rel),
    ("step-trace", EngineEconomics::with_step_trace),
    ("sb-cands", EngineEconomics::with_sb_cands),
    ("sb-total", EngineEconomics::with_sb_total),
    ("dual-bloom-cap", EngineEconomics::with_dual_bloom_cap),
    ("prop-sweeps", EngineEconomics::with_prop_sweeps),
    ("prop-queue", EngineEconomics::with_prop_queue),
    ("splns-exposed", EngineEconomics::with_splns_exposed),
    ("splns-budget", EngineEconomics::with_splns_budget),
    ("ms-walk-moves", EngineEconomics::with_ms_walk_moves),
    ("gub-meas-every", EngineEconomics::with_gub_meas_every),
    ("drought-dive", EngineEconomics::with_drought_dive),
];

const FLOAT_BUILDERS: &[(&str, FloatBuilder)] = &[
    ("splns-stall-secs", EngineEconomics::with_splns_stall_secs),
    ("flip-share", EngineEconomics::with_flip_lns_share),
    ("presolve-share", EngineEconomics::with_presolve_share),
    ("diag-cost-perturb", EngineEconomics::with_diag_cost_perturb),
];

pub fn apply(flags: &Flags, mut opts: SolveOpts) -> Result<SolveOpts, String> {
    let debug = crate::debug_flags::MilpDebugFlags {
        lnp_probe: flags
            .get("lnp-probe")
            .map(|v| &*Box::leak(v.clone().into_boxed_str())),
        kernel_scan_dir: flags
            .get("kernel-scan-dir")
            .map(|v| &*Box::leak(v.clone().into_boxed_str())),
        trace: flags.has("trace"),
        ms_dive_trace: flags.has("ms-dive-trace"),
        coef_tighten_debug: flags.has("coef-tighten-debug"),
        sym_debug: flags.has("sym-debug"),
        shape_census: flags.has("shape-census"),
        sep_screen_audit: flags.has("sep-screen-audit"),
    };
    if debug != crate::debug_flags::MilpDebugFlags::default() {
        let _ = crate::debug_flags::set_milp_debug_flags(debug);
    }
    if flags.has("no-structure-route") {
        opts = opts.with_structure_routing(false);
    }
    let mut engine = EngineEconomics::default();
    let mut touched = false;
    for &(switch, apply, value) in BOOL_BUILDERS {
        if flags.has(switch) {
            engine = apply(engine, value);
            touched = true;
        }
    }
    for &(flag, apply) in USIZE_BUILDERS {
        if let Some(value) = flags.get(flag) {
            let value = value
                .parse::<usize>()
                .map_err(|_| format!("--{flag} needs an integer"))?;
            engine = apply(engine, value);
            touched = true;
        }
    }
    for &(flag, apply) in FLOAT_BUILDERS {
        if let Some(value) = flags.get(flag) {
            let value = value
                .parse::<f64>()
                .map_err(|_| format!("--{flag} needs a number"))?;
            engine = apply(engine, value)
                .map_err(|_| format!("--{flag} must be finite and non-negative"))?;
            touched = true;
        }
    }
    if let Some(value) = flags.get("flip-solve") {
        let mode = match value.as_str() {
            "auto" => crate::FlipSolveMode::Auto,
            "sparse" => crate::FlipSolveMode::Sparse,
            "dense" => crate::FlipSolveMode::Dense,
            _ => return Err("--flip-solve must be auto, sparse or dense".to_string()),
        };
        engine = engine.with_flip_solve(mode);
        touched = true;
    }
    if let Some(value) = flags.get("fc-mode") {
        let mode = value
            .parse::<usize>()
            .map_err(|_| "--fc-mode needs an integer".to_string())?;
        engine = engine
            .with_fc_mode(mode)
            .map_err(|_| "--fc-mode must be 0..=3".to_string())?;
        touched = true;
    }
    for (flag, apply) in [
        (
            "sat-stop-secs",
            EngineEconomics::with_saturation_stop_floor
                as fn(EngineEconomics, std::time::Duration) -> EngineEconomics,
        ),
        ("flip-cap-secs", EngineEconomics::with_flip_lns_cap),
    ] {
        if let Some(value) = flags.get(flag) {
            let secs = value
                .parse::<f64>()
                .ok()
                .filter(|s| s.is_finite() && *s >= 0.0)
                .ok_or_else(|| format!("--{flag} needs a non-negative number of seconds"))?;
            engine = apply(engine, std::time::Duration::from_secs_f64(secs));
            touched = true;
        }
    }
    for (flag, apply) in [
        (
            "sym-branch-band",
            EngineEconomics::with_sym_branch_band as fn(EngineEconomics, f64) -> EngineEconomics,
        ),
        ("dual-perturb", EngineEconomics::with_dual_perturb),
        ("cert-grace-secs", EngineEconomics::with_cert_grace_secs),
        ("pump-share", EngineEconomics::with_pump_share),
        ("setpart-share", EngineEconomics::with_setpart_share),
        ("heur-share", EngineEconomics::with_heur_share),
    ] {
        if let Some(value) = flags.get(flag) {
            let v = value
                .parse::<f64>()
                .map_err(|_| format!("--{flag} needs a number"))?;
            engine = apply(engine, v);
            touched = true;
        }
    }
    if let Some(value) = flags.get("bumpdiff-lanes") {
        let (a, b) = value
            .split_once(',')
            .and_then(|(a, b)| {
                Some((
                    a.trim().parse::<usize>().ok()?,
                    b.trim().parse::<usize>().ok()?,
                ))
            })
            .ok_or_else(|| "--bumpdiff-lanes needs a,b".to_string())?;
        engine = engine
            .with_bumpdiff_lanes(a, b)
            .map_err(|_| "--bumpdiff-lanes lanes must be 0..=2 and distinct".to_string())?;
        touched = true;
    }
    if let Some(value) = flags.get("sym-mode") {
        let mode = match value.as_str() {
            "orbital" => 0,
            "rows" => 1,
            "off" => 2,
            _ => return Err("--sym-mode must be orbital, rows or off".to_string()),
        };
        engine = engine
            .with_sym_mode(mode)
            .map_err(|_| "--sym-mode out of range".to_string())?;
        touched = true;
    }
    if let Some(value) = flags.get("rins") {
        let arm = value
            .parse::<usize>()
            .map_err(|_| "--rins needs an integer".to_string())?;
        engine = engine
            .with_rins_arm(arm)
            .map_err(|_| "--rins must be 1 (pump), 2 (submip) or 3 (fj)".to_string())?;
        touched = true;
    }
    if let Some(value) = flags.get("sat-stop-mult") {
        let mult = value
            .parse::<f64>()
            .map_err(|_| "--sat-stop-mult needs a number".to_string())?;
        engine = engine
            .with_saturation_stop_multiplier(mult)
            .map_err(|_| "--sat-stop-mult must be finite and non-negative".to_string())?;
        touched = true;
    }
    if let Some(value) = flags.get("child-order") {
        let mode = match value.as_str() {
            "away" => 0,
            "up" => 1,
            "dn" => 2,
            "lp" => 3,
            _ => return Err("--child-order must be away, up, dn or lp".to_string()),
        };
        engine = engine
            .with_child_order(mode)
            .map_err(|_| "--child-order out of range".to_string())?;
        touched = true;
    }
    if let Some(value) = flags.get("ft-spike") {
        let arm = match value.as_str() {
            "dense" => 1,
            "sparse" => 2,
            _ => return Err("--ft-spike must be dense or sparse".to_string()),
        };
        engine = engine
            .with_ft_spike(arm)
            .map_err(|_| "--ft-spike out of range".to_string())?;
        touched = true;
    }
    if let Some(value) = flags.get("cut-eff-floor") {
        let floor = value
            .parse::<f64>()
            .map_err(|_| "--cut-eff-floor needs a number".to_string())?;
        engine = engine
            .with_cut_eff_floor(floor)
            .map_err(|_| "--cut-eff-floor must be finite and non-negative".to_string())?;
        touched = true;
    }
    if let Some(value) = flags.get("ng-branch-pct") {
        let pct = value
            .parse::<f64>()
            .map_err(|_| "--ng-branch-pct needs a number".to_string())?;
        engine = engine
            .with_ng_branch_pct(pct)
            .map_err(|_| "--ng-branch-pct must be finite and non-negative".to_string())?;
        touched = true;
    }
    if let Some(value) = flags.get("dual-bypass-mode") {
        let mode = value
            .parse::<usize>()
            .map_err(|_| "--dual-bypass-mode needs an integer".to_string())?;
        engine = engine
            .with_dual_bypass(mode)
            .map_err(|_| "--dual-bypass-mode must be 0, 1 or 2".to_string())?;
        touched = true;
    }
    if let Some(value) = flags.get("eager-perturb-mode") {
        let mode = value
            .parse::<usize>()
            .map_err(|_| "--eager-perturb-mode needs an integer".to_string())?;
        engine = engine
            .with_eager_perturb(mode)
            .map_err(|_| "--eager-perturb-mode must be 0, 1 or 2".to_string())?;
        touched = true;
    }
    if let Some(value) = flags.get("chain-devex") {
        let mode = value
            .parse::<usize>()
            .map_err(|_| "--chain-devex needs an integer".to_string())?;
        engine = engine
            .with_chain_devex(mode)
            .map_err(|_| "--chain-devex must be 0, 1 or 2".to_string())?;
        touched = true;
    }
    if let Some(value) = flags.get("ft-growth-tol") {
        let tolerance = value
            .parse::<f64>()
            .map_err(|_| "--ft-growth-tol needs a number".to_string())?;
        engine = engine
            .with_ft_growth_tol(tolerance)
            .map_err(|_| "--ft-growth-tol must be finite and positive".to_string())?;
        touched = true;
    }
    if touched {
        opts = opts.with_engine(engine);
    }
    Ok(opts)
}
