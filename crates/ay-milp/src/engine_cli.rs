// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Typed engine-economics CLI overrides shared by `ay-milp` and measurement
//! drivers, replacing the retired `AY_MILP_*` environment spellings.

use crate::{EngineEconomics, SolveOpts};

type BoolBuilder = fn(EngineEconomics, bool) -> EngineEconomics;
type UsizeBuilder = fn(EngineEconomics, usize) -> EngineEconomics;
type FloatBuilder = fn(EngineEconomics, f64) -> Result<EngineEconomics, crate::EngineConfigError>;

/// Dependency-free argument bag: known value and switch flags plus positionals;
/// everything else is refused.
pub struct Flags {
    pub positional: Vec<String>,
    named: Vec<(String, String)>,
    switches: Vec<String>,
}

impl Flags {
    /// Parse `args`; names in `value_flags` take a value, names in
    /// `switch_flags` are bare switches, and an unrecognised `--flag` is an
    /// ERROR.
    ///
    /// # Why an unknown flag cannot be tolerated
    ///
    /// This parser fronts a measurement instrument. It formerly accepted an
    /// unknown switch such as `--devx` as a no-op, silently comparing one arm
    /// twice. An unknown value flag could instead leak its value into the seed
    /// path positional and turn a misparse into a missing datum.
    ///
    /// `tests/knob_census.rs` closed the other half (a flag whose knob has no
    /// carrier); this closes the parser half.
    ///
    /// A bare `--` ends flag parsing: everything after it is positional,
    /// which is how a path that starts with `--` gets through.
    ///
    /// # Errors
    ///
    /// A message when a flag is unknown (naming it, and the nearest known
    /// spelling when there is one), when a value flag is missing its value,
    /// or when a switch was given one.
    pub fn parse(
        args: &[String],
        value_flags: &[&str],
        switch_flags: &[&str],
    ) -> Result<Self, String> {
        let mut f = Flags {
            positional: Vec::new(),
            named: Vec::new(),
            switches: Vec::new(),
        };
        let mut i = 0;
        let mut only_positional = false;
        while i < args.len() {
            let a = &args[i];
            match a.strip_prefix("--") {
                Some(rest) if !only_positional => {
                    if rest.is_empty() {
                        only_positional = true;
                        i += 1;
                        continue;
                    }
                    let (name, inline) = match rest.split_once('=') {
                        Some((n, v)) => (n, Some(v.to_string())),
                        None => (rest, None),
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
                    } else if switch_flags.contains(&name) {
                        if inline.is_some() {
                            return Err(format!("--{name} takes no value"));
                        }
                        f.switches.push(name.to_string());
                    } else {
                        return Err(unknown_flag(name, value_flags, switch_flags));
                    }
                }
                _ => f.positional.push(a.clone()),
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

    /// Every flag name given on the command line — values and bare switches
    /// alike, deduplicated and sorted.
    ///
    /// The `ay-milp diag` front door reads this to REFUSE an engine flag on a
    /// diagnostic mode that threads no [`SolveOpts`], where the flag would
    /// otherwise parse and change nothing. A front door that accepts a flag it
    /// cannot honour is the exact failure this module exists to stop, and
    /// widening a parser is how it gets reintroduced.
    #[must_use]
    pub fn names_given(&self) -> Vec<&str> {
        let mut names: Vec<&str> = self
            .named
            .iter()
            .map(|(n, _)| n.as_str())
            .chain(self.switches.iter().map(String::as_str))
            .collect();
        names.sort_unstable();
        names.dedup();
        names
    }
}

/// The refusal, spelled so a human can act on it in one read.
///
/// A misspelled measurement flag is the failure this whole module exists to
/// stop, and the overwhelmingly common case is one wrong character, so the
/// message names the nearest known flag when there is one.
fn unknown_flag(name: &str, value_flags: &[&str], switch_flags: &[&str]) -> String {
    match nearest(name, value_flags, switch_flags) {
        Some(near) => format!(
            "unknown flag `--{name}` — did you mean `--{near}`? \
             (this run was REFUSED rather than measured under a flag that does nothing)"
        ),
        None => format!(
            "unknown flag `--{name}` \
             (this run was REFUSED rather than measured under a flag that does nothing)"
        ),
    }
}

/// The closest known flag, if one is close enough to be a plausible typo.
///
/// The tolerance grows with the name's length — one edit on a four-character
/// flag is a different flag, three on a twenty-character one is a slip.
fn nearest<'a>(name: &str, value_flags: &[&'a str], switch_flags: &[&'a str]) -> Option<&'a str> {
    let budget = match name.len() {
        0..=4 => 1,
        5..=8 => 2,
        _ => 3,
    };
    value_flags
        .iter()
        .chain(switch_flags)
        .map(|&candidate| (edit_distance(name, candidate), candidate))
        .filter(|&(distance, _)| distance <= budget)
        // Ties go to the shorter name, then alphabetically: a deterministic
        // message is a message a test can pin.
        .min_by_key(|&(distance, candidate)| (distance, candidate.len(), candidate))
        .map(|(_, candidate)| candidate)
}

/// Levenshtein distance, two rows. Flag names are tens of bytes and this runs
/// only on the error path, so the quadratic is free and a real edit-distance
/// crate would be a dependency for nothing.
fn edit_distance(a: &str, b: &str) -> usize {
    let b: Vec<char> = b.chars().collect();
    let mut prev: Vec<usize> = (0..=b.len()).collect();
    let mut cur = vec![0usize; b.len() + 1];
    for (i, ca) in a.chars().enumerate() {
        cur[0] = i + 1;
        for (j, &cb) in b.iter().enumerate() {
            let substitute = prev[j] + usize::from(ca != cb);
            cur[j + 1] = substitute.min(prev[j + 1] + 1).min(cur[j] + 1);
        }
        std::mem::swap(&mut prev, &mut cur);
    }
    prev[b.len()]
}

/// Bare switches [`apply`] reads that are not `EngineEconomics` builders: the
/// diagnostic taps lowered into [`crate::debug_flags::MilpDebugFlags`] and the
/// structure-routing opt-out.
pub const DEBUG_SWITCHES: &[&str] = &[
    "trace",
    "ms-dive-trace",
    "coef-tighten-debug",
    "sym-debug",
    "shape-census",
    "sep-screen-audit",
    "no-structure-route",
];

/// Every bare switch [`apply`] understands — the switch half of what
/// [`VALUE_FLAGS`] is for values.
///
/// Built from the builder table itself rather than restated, so a flag added
/// to `BOOL_BUILDERS` is accepted by every caller of [`Flags::parse`] that
/// passes this, and a flag deleted there stops being accepted, with no second
/// list to forget.
#[must_use]
pub fn switch_flags() -> Vec<&'static str> {
    BOOL_BUILDERS
        .iter()
        .map(|&(name, _, _)| name)
        .chain(DEBUG_SWITCHES.iter().copied())
        .collect()
}

/// The flags [`apply`] reads by hand, outside the four builder tables.
///
/// Kept next to [`applied_flags`] because that function is a CONTRACT — "these
/// names, and only these, change the engine" — and the hand-rolled arms in
/// `apply` are the half no table can enumerate. `hand_rolled_names_are_declared`
/// in this module's tests pins every entry to [`VALUE_FLAGS`]; a new hand-rolled
/// arm that is not listed here makes `ay-milp diag` refuse a flag it could have
/// honoured, which is a loud failure rather than a silent one.
const HAND_ROLLED: &[&str] = &[
    "lnp-probe",
    "kernel-scan-dir",
    "flip-solve",
    "fc-mode",
    "sat-stop-secs",
    "flip-cap-secs",
    "sym-branch-band",
    "dual-perturb",
    "setpart-share",
    "bumpdiff-lanes",
    "sym-mode",
    "rins",
    "sat-stop-mult",
    "child-order",
    "ft-spike",
    "cut-eff-floor",
    "ng-branch-pct",
    "dual-bypass-mode",
    "eager-perturb-mode",
    "harris-rt",
    "chain-devex",
    "ft-growth-tol",
];

/// Every flag name [`apply`] actually CONSUMES — values and switches together.
///
/// [`VALUE_FLAGS`] is a superset: it also carries the `solve` subcommand's own
/// names (`--emit-cert`, `--require`, `--threads`, `--seed`, …), which `apply`
/// never reads. A caller that wants to accept "the engine flags" and refuse
/// everything else — `ay-milp diag` does — needs the smaller set, because
/// accepting a flag one cannot honour is precisely the dead-flag failure.
#[must_use]
pub fn applied_flags() -> Vec<&'static str> {
    BOOL_BUILDERS
        .iter()
        .map(|&(name, _, _)| name)
        .chain(DEBUG_SWITCHES.iter().copied())
        .chain(USIZE_BUILDERS.iter().map(|&(name, _)| name))
        .chain(FLOAT_BUILDERS.iter().map(|&(name, _)| name))
        .chain(HAND_ROLLED.iter().copied())
        .collect()
}

/// Parse `args` against exactly what [`apply`] can carry, plus a surface's own
/// names — the parse table a MEASUREMENT HARNESS wants.
///
/// # The defect this stops
///
/// [`VALUE_FLAGS`] is not the harness table. It is the `ay-milp solve`
/// subcommand's table, and it is a strict superset of [`applied_flags`]: it
/// also carries the FOURTEEN names only `solve` itself reads (`--emit-cert`,
/// `--require`, `--threads`, `--seed`, `--format`, `--memory-budget`,
/// `--opt-tree-secs`, …). Every harness that handed `VALUE_FLAGS` to
/// [`Flags::parse`] therefore ACCEPTED those fourteen and could honour none of
/// them, because it is `apply` — not the parser — that turns an accepted name
/// into a `SolveOpts`.
///
/// Measured on `6f45bcf66`, three interleaved reps each, load 57-69 on a
/// 14-core box (counts and file sizes only, no wall figure load-coupled):
///
///   * `cert_probe m 5 --require optimal` printed `require_certificates=0`
///     and `evidence=witness+uncertified-dual-bound` on 3 of 3, while
///     `cert_probe m 5 1` — the same setting via the positional the harness
///     really reads — printed `require_certificates=1` and
///     `evidence=witness-only` on 3 of 3. The flag did not merely do nothing:
///     it named one arm and measured the other, on the harness whose entire
///     purpose is pricing certificate requirements.
///   * `cert_probe m 5 --emit-cert F` exited 0 and left F ABSENT on 3 of 3,
///     while `ay-milp solve m 5 --emit-cert F` wrote 11,304 bytes on 3 of 3.
///
/// A surface calling this instead gets those names REFUSED by name, with the
/// nearest known spelling, which is the loud failure the silent one deserved.
///
/// # Errors
///
/// Whatever [`Flags::parse`] returns: an unknown flag, a value flag with no
/// value, or a switch given one.
pub fn parse_applied(
    args: &[String],
    own_value_flags: &[&str],
    own_switch_flags: &[&str],
) -> Result<Flags, String> {
    let engine_switches = switch_flags();
    let mut switches: Vec<&str> = engine_switches.clone();
    switches.extend(own_switch_flags.iter().copied());
    // `applied_flags` minus the switch half is the value half — derived, not
    // restated, so a builder moved between tables cannot leave a name behind
    // in one list and absent from the other.
    let mut values: Vec<&str> = applied_flags()
        .into_iter()
        .filter(|name| !engine_switches.contains(name))
        .collect();
    values.extend(own_value_flags.iter().copied());
    values.sort_unstable();
    values.dedup();
    switches.sort_unstable();
    switches.dedup();
    Flags::parse(args, &values, &switches)
}

/// The `ay-milp solve` subcommand's parse table.
///
/// NOT the table for a measurement harness — see [`parse_applied`], which is.
/// A name belongs here only if `solve` itself reads it or [`apply`] carries it;
/// `--check-sol` and `--dual-cutoff` were here and satisfied neither, so
/// `ay-milp solve --dual-cutoff 0.0` parsed cleanly and ran the unflagged arm
/// (byte-identical stdout and an identical 11,304-byte certificate against no
/// flag at all, 2 interleaved reps on `6f45bcf66`), while the one harness that
/// does read the name, `mps_solve`, echoed
/// `--dual-cutoff: 0.0 (file frame) -> 0 (model frame, obj_scale 1)` on both.
/// Both now live in `mps_solve`'s own table, so `solve` refuses them by name.
pub const VALUE_FLAGS: &[&str] = &[
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
    "opt-tree-secs",
    "opt-tree-leaves",
    "opt-tree-work",
    "opt-tree-grid",
    "root-dual-rim",
    "root-dual-secs",
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
    "harris-rt",
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
    // CENSUS CARRIERS: flags that parsed but changed nothing until `opts/carriers.rs`
    // gave their knobs a writer. See `tests/knob_census.rs`.
    "node-cut-slots",
    "node-cut-every",
    "node-gmi",
    "node-gmi-every",
    "scale",
    "cut-topk",
    "sb-probe-iters",
    "root-probe-cap",
    "root-probe-clique-cap",
    "node-cut-batch",
    "node-cut-age",
    "ms-dive-steps",
    "gmi-max-rows",
    "chain-probe",
    "bump-lu-min",
    "cold-lu-eta-rebuilds",
    "adopt-ft-max-rows",
    "refactor-every",
    "eta-cap-mult",
    "lu-max-fill-nnz",
    "node-gmi-margin",
    "dive-probe-secs",
    "rens-window",
    "root-probe-share",
    "prop-first",
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
        "no-tall-cold-dual",
        |engine, _| engine.with_tall_cold_dual(crate::TallColdDualMode::Disabled),
        false,
    ),
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
    (
        "root-closure-presolve",
        EngineEconomics::with_root_closure_presolve,
        true,
    ),
    ("tableau-mir", EngineEconomics::with_tableau_mir, true),
    ("mir-agg-root", EngineEconomics::with_mir_agg_root, true),
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
    ("auto-margin", EngineEconomics::with_auto_margin, true),
    ("dense-gmi-lu", EngineEconomics::with_dense_gmi_lu, true),
    ("no-chain-shape", EngineEconomics::with_chain_shape, false),
    (
        "no-chain-preorder",
        EngineEconomics::with_chain_preorder,
        false,
    ),
    ("no-bump-lu", EngineEconomics::with_bump_lu, false),
    ("no-float", EngineEconomics::with_float_lane, false),
    // CENSUS CARRIERS: flags that parsed but changed nothing until `opts/carriers.rs`
    // gave their knobs a writer. See `tests/knob_census.rs`.
    ("singleton-sub", EngineEconomics::with_singleton_sub, true),
    ("node-cut-eager", EngineEconomics::with_node_cut_eager, true),
    ("amo-multiway", EngineEconomics::with_amo_multiway, true),
    ("node-rc", EngineEconomics::with_node_rc, true),
    ("no-rc-cap-guard", EngineEconomics::with_rc_cap_guard, false),
    ("tri-crash-all", EngineEconomics::with_tri_crash_all, true),
    ("sym-branch", EngineEconomics::with_sym_branch, true),
    ("no-sym-branch", EngineEconomics::with_sym_branch, false),
    ("stab-orbit", EngineEconomics::with_stab_orbit, true),
    ("orbitope-dyn", EngineEconomics::with_orbitope_dyn, true),
    ("no-tree-floor", EngineEconomics::with_tree_floor, false),
    (
        "no-tree-bound-outcome",
        EngineEconomics::with_tree_bound_outcome,
        false,
    ),
    ("no-root-floor", EngineEconomics::with_root_floor, false),
    ("cover-minimal", EngineEconomics::with_cover_minimal, true),
    ("gub-clique", EngineEconomics::with_gub_clique, true),
    ("gmi-cut-trace", EngineEconomics::with_gmi_cut_trace, true),
    ("cond-tighten", EngineEconomics::with_cond_tighten, true),
    ("mod-k", EngineEconomics::with_mod_k, true),
    ("knap-dbg", EngineEconomics::with_knap_dbg, true),
    ("cold-dual-all", EngineEconomics::with_cold_dual_all, true),
    ("cut-warm", EngineEconomics::with_cut_warm, true),
    ("rlt", EngineEconomics::with_rlt, true),
    (
        "dive-commit-stopped",
        EngineEconomics::with_dive_commit_stopped,
        true,
    ),
    ("no-root-warm", EngineEconomics::with_root_warm, false),
    (
        "orbitope-branch",
        EngineEconomics::with_orbitope_branch,
        true,
    ),
    ("orbitope-ilv", EngineEconomics::with_orbitope_ilv, true),
    (
        "orbitope-branch-dyn",
        EngineEconomics::with_orbitope_branch_dyn,
        true,
    ),
    ("node-cut-local", EngineEconomics::with_node_cut_local, true),
    ("no-cond-scout", EngineEconomics::with_cond_scout, false),
    ("hybrid-pb-lp", EngineEconomics::with_hybrid_pb_lp, true),
    ("attrib", EngineEconomics::with_attrib, true),
    ("acensus", EngineEconomics::with_acensus, true),
    ("hybrid-term", EngineEconomics::with_hybrid_term, true),
    (
        "root-probe-no-lp-rank",
        EngineEconomics::with_root_probe_lp_rank,
        false,
    ),
    ("ms-dive", EngineEconomics::with_ms_dive, true),
    ("mas74-plunge", EngineEconomics::with_mas74_plunge, true),
    ("no-mas74-plunge", EngineEconomics::with_mas74_plunge, false),
    ("relax-lift", EngineEconomics::with_relax_lift, true),
    ("devex", EngineEconomics::with_force_devex, true),
    ("bump-btf", EngineEconomics::with_bump_btf, true),
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
    // CENSUS CARRIERS: flags that parsed but changed nothing until `opts/carriers.rs`
    // gave their knobs a writer. See `tests/knob_census.rs`.
    ("node-cut-slots", EngineEconomics::with_node_cut_slots),
    ("node-cut-every", EngineEconomics::with_node_cut_every),
    ("node-gmi", EngineEconomics::with_node_gmi),
    ("node-gmi-every", EngineEconomics::with_node_gmi_every),
    ("scale", EngineEconomics::with_scale),
    ("cut-topk", EngineEconomics::with_cut_topk),
    ("sb-probe-iters", EngineEconomics::with_sb_probe_iters),
    ("root-probe-cap", EngineEconomics::with_root_probe_cap),
    (
        "root-probe-clique-cap",
        EngineEconomics::with_root_probe_clique_cap,
    ),
    ("node-cut-batch", EngineEconomics::with_node_cut_batch),
    ("node-cut-age", EngineEconomics::with_node_cut_age),
    ("ms-dive-steps", EngineEconomics::with_ms_dive_steps),
    ("gmi-max-rows", EngineEconomics::with_gmi_max_rows),
    ("chain-probe", EngineEconomics::with_chain_probe),
    ("bump-lu-min", EngineEconomics::with_bump_lu_min),
    (
        "cold-lu-eta-rebuilds",
        EngineEconomics::with_cold_lu_eta_rebuilds,
    ),
    ("adopt-ft-max-rows", EngineEconomics::with_adopt_ft_max_rows),
    ("refactor-every", EngineEconomics::with_refactor_every),
    ("eta-cap-mult", EngineEconomics::with_eta_cap_mult),
    ("lu-max-fill-nnz", EngineEconomics::with_lu_max_fill_nnz),
];

const FLOAT_BUILDERS: &[(&str, FloatBuilder)] = &[
    ("splns-stall-secs", EngineEconomics::with_splns_stall_secs),
    ("flip-share", EngineEconomics::with_flip_lns_share),
    ("presolve-share", EngineEconomics::with_presolve_share),
    ("cert-grace-secs", EngineEconomics::with_cert_grace_secs),
    ("pump-share", EngineEconomics::with_pump_share),
    ("heur-share", EngineEconomics::with_heur_share),
    ("diag-cost-perturb", EngineEconomics::with_diag_cost_perturb),
    // CENSUS CARRIERS: flags that parsed but changed nothing until `opts/carriers.rs`
    // gave their knobs a writer. See `tests/knob_census.rs`.
    ("node-gmi-margin", EngineEconomics::with_node_gmi_margin),
    ("dive-probe-secs", EngineEconomics::with_dive_probe_secs),
    ("rens-window", EngineEconomics::with_rens_window),
    ("root-probe-share", EngineEconomics::with_root_probe_share),
    ("prop-first", EngineEconomics::with_prop_first),
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
            engine = apply(engine, value).map_err(|error| format!("--{flag}: {error}"))?;
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
        ("setpart-share", EngineEconomics::with_setpart_share),
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
    if let Some(value) = flags.get("harris-rt") {
        let mode = value
            .parse::<usize>()
            .map_err(|_| "--harris-rt needs an integer".to_string())?;
        engine = engine
            .with_harris_rt(mode)
            .map_err(|_| "--harris-rt must be 0, 1 or 2".to_string())?;
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

#[cfg(test)]
#[path = "engine_cli/tests.rs"]
mod tests;
