// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// #14 factor-dense unlock, DEFAULT ON for density >= 90
/// (`AY_AB_FACTOR_DENSE=0` disables): factorization is allowed through the
/// dense-formula skip (the absolute var/clause caps and factor's own — now
/// honestly accounted — effort budget still apply). Dense ternary formulas
/// are the most factorable class; the shared density skip conflated "dense"
/// with "unprofitable" and blanket-disabled the one technique that cracks
/// them. Not a soundness switch — factorization is proof-emitting and
/// satisfiability-preserving; scheduling changes cost only.
///
/// WHY THE DENSITY BAND: the 32-instance main-track dense A/B (every
/// affected instance = density>50 within the absolute caps, off-vs-on at
/// 100s, 0 verdict disagreements) split cleanly by density. Gains at
/// density >= 100: 82851650 (103) timeout→unsat 47s — the class flagship —
/// and a2fe3213 (171) timeout→sat 54s. Losses at density ~60: 43fbacb2 and
/// 16564a6a (both 60.3) flipped sat@4.2s/67s → timeout when factored (the
/// extension-variable restructuring hurts SAT search on the moderate-density
/// band). All other instances neutral. A flat flip is +2/−2 (net zero); the
/// >=90 band keeps both gains and excludes both losses by construction:
/// in-band +2/−0. Below the band the original density skip applies
/// unchanged. Same landing discipline as LNH: opt-in → measured
/// differential → gated default-on. Cached OnceLock per the #8506
/// no-per-call-syscall convention.
///
/// NEGATIVE RESULT — do not lower without new evidence: after the
/// incremental-PQ rework cut the factor pass 16x (47s → ~3s), the sub-90
/// band was RE-MEASURED (15 instances, band=90 vs band=50 via the env
/// knob, 100s, 0 disagreements): net zero again, and the gains/losses
/// INTERLEAVE in density — 2de9b799 (d=57.4) gains unknown→sat@63s while
/// 43fbacb2 (d=60.3) loses sat@4.3s→timeout exactly as it did under the
/// 47s pass. So 43fbacb2's loss was never the factoring tax: the
/// extension-variable restructuring itself hurts that instance's SAT
/// search, and no density edge below 90 separates winners from losers. A
/// finer-than-density predictor (e.g. post-factor clause-reduction ratio)
/// would be needed to harvest the sub-90 stragglers.
///
/// SECOND NEGATIVE RESULT — the census predictor was then MEASURED and does
/// NOT separate either: a read-only factoring dry-run on the full win/loss
/// set showed the loser 43fbacb2 (net reduction 0.545) sitting BETWEEN
/// winners (0.296 / 0.471 / 0.988) on every candidate metric (net
/// reduction, deleted/active, factored/vars, ext-var cost per deleted
/// clause). The density-60 winner (2de9b799) and loser (43fbacb2) are
/// near-twin formulas whose factoring profiles agree within ~15%; the
/// borderline twin 16564a6a matches the loser to 0.2%. The win/loss split
/// in that family is search variance, not census-predictable. (Side
/// finding: density predicts FACTORABILITY in neither direction — 9b998be
/// at 83 and 04648cef at 164 both factor ZERO clauses.) Remaining path to
/// the sub-90 stragglers, if ever needed: racing/portfolio (run factored
/// and unfactored under a budget split) — a different architecture, not a
/// static predictor.
pub(in crate::solver) const FACTOR_DENSE_MIN_DENSITY: f64 = 90.0;

/// The live band edge: [`FACTOR_DENSE_MIN_DENSITY`] unless overridden via
/// (B3: the env override is deleted — the 90.0 default was
/// calibrated when the factor pass cost 47s; the incremental-PQ rework cut
/// that to ~3s, so the profitable edge is being re-measured). Cached
/// OnceLock per the #8506 no-per-call-syscall convention.
pub(in crate::solver) fn factor_dense_min_density() -> f64 {
    // B3: the AY_FACTOR_DENSE_MIN_DENSITY env override is deleted; the constant stands.
    FACTOR_DENSE_MIN_DENSITY
}

/// Env kill-switch for the factor-dense unlock (see
/// [`FACTOR_DENSE_MIN_DENSITY`]). Default ON; `AY_AB_FACTOR_DENSE=0`
/// restores the blanket density skip.
pub(in crate::solver) fn factor_dense_enabled() -> bool {
    // B26: CLI-owned opt-out (--sat-no-factor-dense); env retired.
    !ay_core::sat_ab_switches().no_factor_dense
}

/// Env kill-switch for the dense-band factor init-budget raise (see
/// [`FACTOR_DENSE_INIT_TICKS`]). DEFAULT ON; `--sat-no-factor-dense-init`
/// restores the sparse [`FACTOR_INIT_TICKS`] (500M) first-call bonus on ALL
/// bands. Only the first (`factor_rounds == 0`) factoring call in the dense
/// band (density >= [`factor_dense_min_density`]) is affected — later
/// inprocessing calls already cap at [`FACTOR_MAX_EFFORT`] with no bonus.
/// Cached OnceLock per the #8506 no-per-call-syscall convention.
pub(in crate::solver) fn factor_dense_init_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| !ay_core::sat_ab_switches().no_factor_dense_init)
}

/// Dense-band first-call factor init budget: [`FACTOR_DENSE_INIT_TICKS`] (1B)
/// unless overridden via `AY_FACTOR_DENSE_INIT_TICKS` (A/B tuning knob;
/// zero/unparseable is ignored). Cached OnceLock per the #8506
/// no-per-call-syscall convention.
pub(in crate::solver) fn factor_dense_init_ticks() -> u64 {
    // B3: the AY_FACTOR_DENSE_INIT_TICKS env override is deleted; the constant stands.
    FACTOR_DENSE_INIT_TICKS
}

/// Per-call factor effort ceiling: [`FACTOR_MAX_EFFORT`] (1B) unless overridden
/// via `AY_FACTOR_MAX_EFFORT` (measured-infra A/B knob; zero/unparseable is
/// ignored → the constant). DEFAULT-INERT: with the env unset this returns
/// exactly [`FACTOR_MAX_EFFORT`], so the `effort.min(..)` clamp at
/// factorize.rs is byte-identical to the pre-knob code and the certified board
/// is untouched.
///
/// WHY THIS EXISTS (huge-binary-dense measurement infra, NOT a default flip):
/// the hard 1B per-call clamp is the binding ceiling above the dense-init
/// bonus — even a raised `AY_FACTOR_DENSE_INIT_TICKS` is clipped to 1B here, so
/// the density-264 / >0.99-binary cluster (f6a085f3 / 6ff70a3a, ~11M binary
/// clauses) could not be studied without a recompile. This knob unclamps the
/// ceiling for opt-in A/B runs so the "does draining the factor schedule on
/// the huge-binary band actually SOLVE?" question can be measured directly
/// (pair with `AY_FACTOR_DENSE_INIT_TICKS` and `AY_FACTOR_DENSE_INIT_MAX_CLAUSES`
/// to reach and drain that band).
///
/// MEASURED-NEGATIVE for a default flip (do NOT raise the constant): draining
/// the f6a085f3/6ff70a3a schedule to ~70K factorings (kissat parity, 96.7%
/// clause collapse) still yields `s UNKNOWN` — the post-factor BVE that
/// kissat's UNSAT depends on never fires (its ~104K-elimination step is gated
/// off by the ORIGINAL 11M-clause count, and the landed post-collapse reopen
/// [`bve_post_collapse_reopens`] is VAR-gated: f6's 42K vars are under
/// [`PREPROCESS_EXPENSIVE_MAX_VARS`], so it does not re-open the clause-count
/// skip), and the ~58s factoring wall (8x-coarser element-tick accounting)
/// eats most of the 120s budget. So this stays a measurement lever only.
///
/// FOLLOW-UP (opt-in `AY_AB_BVE_POST_FACTOR`, see [`bve_post_factor_reopens`]):
/// the CLAUSE-axis analogue of the var-gated post-collapse reopen now exists —
/// it re-derives BVE eligibility on the factor-collapsed active-clause count so
/// BVE actually FIRES on f6's ~371K-clause residual (measured: reopen arms
/// correctly, 70,947 factors / kissat-parity, and BVE eliminates 3,346 vars vs
/// 0 without it). But f6 STILL stays `s UNKNOWN`: AY's BVE hits a structural
/// ceiling of ~1,306 eliminations here vs kissat's 104,496 (binary-dense
/// extension-variable formula; every candidate resolution is net-neutral and
/// the growth-bound-16 guard rejects it), so the formula never closes. The
/// reopen is the correct, proven mechanism but nowhere near sufficient; it
/// ships DEFAULT-OFF measurement-infra only. Closing this cluster needs a
/// fundamentally stronger BVE on the post-factor binary-dense class, not the
/// reopen gate. Cached OnceLock per the #8506 no-per-call-syscall convention.
pub(in crate::solver) fn factor_max_effort() -> u64 {
    // B3: the AY_FACTOR_MAX_EFFORT env override is deleted; the constant stands.
    FACTOR_MAX_EFFORT
}

/// Upper residual-clause bound for the dense-band init raise:
/// [`FACTOR_DENSE_INIT_MAX_CLAUSES`] (3M) unless overridden via
/// `AY_FACTOR_DENSE_INIT_MAX_CLAUSES` (A/B tuning knob; zero/unparseable is
/// ignored). Cached OnceLock per the #8506 no-per-call-syscall convention.
pub(in crate::solver) fn factor_dense_init_max_clauses() -> usize {
    // B3: the AY_FACTOR_DENSE_INIT_MAX_CLAUSES env override is deleted; the constant stands.
    FACTOR_DENSE_INIT_MAX_CLAUSES
}

/// Pure predicate: does the dense-band factor init-budget raise apply at the
/// first factor call? `true` iff the raise is enabled, `density` is in the
/// dense band, AND the residual is small enough (`active_clauses <=
/// max_clauses`) that factoring is the productive small-dense class rather
/// than a marginal huge residual whose extra budget only perturbs search (see
/// [`FACTOR_DENSE_INIT_MAX_CLAUSES`]). Env-free and unit-testable; the env
/// reads are folded in by the caller via [`factor_dense_init_enabled`] /
/// [`factor_dense_init_max_clauses`].
pub(in crate::solver) fn factor_dense_init_applies(
    enabled: bool,
    density: f64,
    active_clauses: usize,
    max_clauses: usize,
) -> bool {
    enabled && density >= factor_dense_min_density() && active_clauses <= max_clauses
}

/// Post-collapse BVE eligibility re-derivation knob
/// (`--sat-no-bve-post-collapse`). DEFAULT ON since 2026-07-10 (collapse+BVE
/// default flip, wf_55735963; measurement wf_2ee873fc/wf_0552d0f0): with the
/// AUTO collapse + sparse-deep stack on the scoreboard protocol
/// (`--competition`, 120s, no proof, main2025), re-deriving BVE eligibility
/// from the collapsed ACTIVE variable count contributed to +7 kissat-agreeing
/// UNSAT flips (e.g. df813fe7 unknown->UNSAT 80s with 188,557 eliminations)
/// with 0 hard lost solves and a provably inert dense band. The unlock stays
/// scoped by `bve_post_collapse_unlock_active()` (LRAT/incremental refusal,
/// collapse requirement, 400K active-var cap, dense re-check), which is
/// exactly the band the measurement validated. Kill-switch
/// `--sat-no-bve-post-collapse` restores the pre-flip opt-in behavior. Cached
/// OnceLock per the #8506 no-per-call-syscall convention.
pub(in crate::solver) fn bve_post_collapse_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| !ay_core::sat_ab_switches().no_bve_post_collapse)
}

/// Re-derived active-variable cap for the post-collapse BVE unlock:
/// [`BVE_POST_COLLAPSE_MAX_VARS`] (600K — see that constant for the measured
/// rationale). (B3: the env override is deleted.)
pub(in crate::solver) fn bve_post_collapse_max_vars() -> usize {
    // B3: the AY_BVE_POST_COLLAPSE_MAX_VARS env override is deleted.
    BVE_POST_COLLAPSE_MAX_VARS
}

/// Pure post-collapse BVE re-eligibility predicate (unit-testable, env-free).
///
/// Returns `true` iff the BVE routes that were closed by the ORIGINAL
/// `num_vars > PREPROCESS_EXPENSIVE_MAX_VARS` gate may be re-opened because
/// the congruence/decompose collapse shrank the ACTIVE variable count under
/// `max_vars`.
///
/// Direction invariant (asserted by tests): this predicate can only OPEN
/// above-cap cases — it is `false` whenever `original_num_vars <=
/// PREPROCESS_EXPENSIVE_MAX_VARS`, so in-band formulas (where
/// `skip_expensive_preprocessing_passes` was never var-driven) see zero
/// behavior change. It is also `false` when the collapse merged nothing
/// (`collapsed_vars == 0`), so instances without substitution structure (the
/// elimination-only controls) are untouched.
pub(in crate::solver) fn bve_post_collapse_reopens(
    enabled: bool,
    original_num_vars: usize,
    rederived_active_vars: usize,
    collapsed_vars: usize,
    max_vars: usize,
) -> bool {
    enabled
        && original_num_vars > PREPROCESS_EXPENSIVE_MAX_VARS
        && collapsed_vars > 0
        && rederived_active_vars <= max_vars
}

/// Post-factor BVE clause-reopen knob (`AY_AB_BVE_POST_FACTOR`).
/// DEFAULT OFF (opt-in measured-infra — MEASURED-NEGATIVE on the class it
/// targets; see [`bve_post_factor_reopens`] and
/// [`BVE_POST_FACTOR_MIN_COLLAPSE_RATIO`]). `=1` arms the clause-axis analogue
/// of the post-collapse reopen: after factoring shrinks the active-clause
/// count below the expensive-pass cap, re-derive BVE eligibility on the
/// COLLAPSED counts so BVE fires on the factored residual. Cached OnceLock per
/// the #8506 no-per-call-syscall convention.
pub(in crate::solver) fn bve_post_factor_enabled() -> bool {
    // B21: the AY_AB_BVE_POST_FACTOR opt-in is retired — its own test called
    // it a measured-negative lever and the HONEST STATUS block records the
    // reopen firing without a solve. The reopen stays compiled-inert.
    false
}

/// Minimum factor-collapse ratio for the post-factor BVE reopen:
/// [`BVE_POST_FACTOR_MIN_COLLAPSE_RATIO`] (8.0). (B3: the env override is
/// deleted.)
pub(in crate::solver) fn bve_post_factor_min_collapse_ratio() -> f64 {
    // B3: the AY_BVE_POST_FACTOR_MIN_RATIO env override is deleted.
    BVE_POST_FACTOR_MIN_COLLAPSE_RATIO
}

/// Pure post-FACTOR BVE re-eligibility predicate (unit-testable, env-free) —
/// the CLAUSE-axis analogue of [`bve_post_collapse_reopens`].
///
/// The post-collapse predicate re-opens BVE when congruence/decompose
/// SUBSTITUTION shrank the ACTIVE VARIABLE count under a cap. But the
/// density-264 huge-binary cluster (f6a085f3: 42K vars, 11.1M clauses)
/// collapses in CLAUSES, not vars: factoring introduces extension variables
/// and deletes ~97% of the binary clauses, dropping active_clauses 11.1M →
/// ~371K while num_vars GROWS (42K → 113K). Its 42K original vars are far
/// under [`PREPROCESS_EXPENSIVE_MAX_VARS`], so the var-gated post-collapse
/// reopen never fires; the two ORIGINAL-clause gates
/// (`skip_expensive_preprocessing_passes` from `num_clauses > max_clauses`,
/// and the dense-skip from density 264) stay latched on the pre-factor
/// counts. This predicate re-derives eligibility on the FACTORED residual.
///
/// Returns `true` iff:
///   - the knob is enabled (default OFF — this whole lever is opt-in), AND
///   - the ORIGINAL active-clause count was ABOVE the expensive-pass cap
///     (`original_active_clauses > max_clauses`) — so it can only OPEN
///     above-cap cases, never touch in-band ones, AND
///   - factoring actually ran (`factored_vars > 0`) — inert when factoring
///     did nothing, AND
///   - the FACTORED residual is under the cap
///     (`rederived_active_clauses <= max_clauses`), AND
///   - the collapse was large-ratio
///     (`original >= min_collapse_ratio * rederived`) — a marginal huge
///     residual cannot arm expensive BVE.
///
/// Direction invariant (asserted by tests, same shape as the post-collapse
/// predicate): can only OPEN above-cap cases (false when
/// `original_active_clauses <= max_clauses`), false when factoring did nothing
/// (`factored_vars == 0`), false on small-ratio collapses. The live
/// dense-skip re-check on the collapsed counts is folded in by the caller
/// (`bve_post_factor_unlock_active`), exactly like the sparse-band and giant-raw
/// unlocks.
pub(in crate::solver) fn bve_post_factor_reopens(
    enabled: bool,
    original_active_clauses: usize,
    rederived_active_clauses: usize,
    factored_vars: usize,
    max_clauses: usize,
    min_collapse_ratio: f64,
) -> bool {
    enabled
        && original_active_clauses > max_clauses
        && factored_vars > 0
        && rederived_active_clauses <= max_clauses
        && original_active_clauses as f64 >= min_collapse_ratio * rederived_active_clauses as f64
}

/// Post-BVE instantiate scheduling gate (`AY_AB_BVE_INST_GATE`, lever 2 of
/// the 2026-07-11 sparse-prize completion round). DEFAULT ON; `=0` restores
/// the historical per-bve_body unbudgeted instantiate.
///
/// WHY: AY runs `instantiate()` at the END OF EVERY `bve_body` call, with no
/// internal budget (per-candidate full BCP over the live watch graph after a
/// full `reconnect_bve_watches(0)`), while kissat has no in-eliminate
/// analogue and CaDiCaL runs it as a rare separate pass. The fast-inner
/// profile on the deep collapse+BVE path measured instantiate at 6.5-13.2s
/// PER bve_body CALL on the ebbda8d9 class — 74-86% of the remaining BVE
/// wall AFTER the O(1) suppress fix — and every second of it runs OUTSIDE
/// the fastelim wall (`bve_body` checks the wall only between elimination
/// rounds; instantiate starts after the loop). One preprocess phase calls
/// bve_body 2-7 times (quick + fastelim + gate passes), so the untracked tax
/// compounds.
///
/// When ON the gate applies two scheduling bounds (soundness-free —
/// instantiate is an optional strengthening pass; its clause replacements
/// remain checked/proof-emitting):
///   1. at most ONE instantiate per elimination phase
///      (`cold.bve_elim_phase_seq` is stamped at run_preprocess_bve and
///      inprocessing-elimination entries; the first productive bve_body in
///      the phase consumes the slot), and
///   2. the run is placed UNDER the same wall the bve_body rounds use: it is
///      skipped when the wall is already exhausted, and its candidate loop
///      breaks at the wall deadline (fastelim: FASTELIM_WALL_CLOCK_LIMIT_SECS
///      or the deep wall, proof-scaled; inprocessing:
///      BVE_INPROCESSING_WALL_LIMIT_MS), so bve_body's TOTAL cost including
///      instantiate is bounded by its wall.
///
/// EXONERATED by the remeasure3 SAT-churn attribution (2026-07, main
/// 8b40f19a): this gate was the prime suspect for the sparse-SAT churn pair
/// but measured clean on both — f25a1df8 gate-on SAT@44.9s vs gate-off
/// SAT@47.2s (equal within run noise), and f406e2b8 produced BOTH SAT and
/// 120s-timeout under EACH gate setting across runs (gate-on: 29.4s/32.4s/
/// TO; gate-off: 34.6s and TO), i.e. its oscillation is protocol-level
/// nondeterminism (see INPROCESSING_ROUND_WALL_LIMIT_MS), not this gate.
/// Do NOT flip this default OFF to chase those instances.
pub(in crate::solver) fn bve_inst_gate_enabled() -> bool {
    // B26: CLI-owned opt-out (--sat-no-bve-inst-gate); env retired.
    !ay_core::sat_ab_switches().no_bve_inst_gate
}

/// Pure qualification predicate for the giant raw-BVE unlock (lever 3 of the
/// 2026-07-11 sparse-prize completion round; env knob `AY_AB_BVE_GIANT_RAW`,
/// route/band arming in `VariantConfig::bve_giant_raw_route_active`).
///
/// The post-collapse unlock (`bve_post_collapse_reopens`) only opens BVE for
/// >200K-var formulas whose ACTIVE count collapsed under the cap via
/// congruence/decompose substitution. Elimination-shaped giants with NO
/// substitution structure (9d7caee5: 1.69M vars, 5.96M clauses, density 3.5,
/// AUTO probe equivalence density 0 — kissat unsat@66s via 93% elimination)
/// can never qualify: no collapse is possible, so no BVE route exists at all
/// above the 150K sparse-band cap. This predicate opens the raw (no-collapse)
/// deep-BVE band instead.
///
/// Returns `true` iff:
///   - the variant-level route/band flag is armed (Default DIMACS non-LRAT,
///     150K < parsed vars <= 2M, parsed clauses <= 8M, parsed density <= 12
///     — see the variant predicate for the band rationale), and
///   - the collapse substituted NOTHING (`collapsed_vars == 0`): collapsed
///     instances belong to the post-collapse lever; this keeps the two
///     unlocks disjoint by construction (07cea7a6/ebbda8d9/df813fe7 all
///     collapse and stay on their measured path), and
///   - the live dense-skip guard re-check passes on the CURRENT counts, so
///     the unlock can never run expensive BVE on a formula that densified
///     after the header-derived flag was set (same defense the sparse-band
///     unlock re-checks).
pub(in crate::solver) fn bve_giant_raw_qualifies(
    route_armed: bool,
    collapsed_vars: usize,
    active_clauses: usize,
    active_vars: usize,
) -> bool {
    if !route_armed || collapsed_vars != 0 {
        return false;
    }
    let density = if active_vars > 0 {
        active_clauses as f64 / active_vars as f64
    } else {
        0.0
    };
    !PreprocessPolicy::skip_dense_formula(active_clauses, density)
}

/// Formula-density cap for the DEFAULT-ON AUTO collapse path (2026-07-11
/// dense-band regression fix — certified remeasure2 attribution, dense band
/// 23→19 at main 0bb876d9). Pure predicate (env-free, unit-tested below):
/// `true` means this solve must take the EARLY dense disarm in
/// [`Solver::compute_preprocess_policy`] — AUTO-armed decompose/congruence
/// off and `cold.subst_auto_collapse` cleared BEFORE the policy consults
/// them, so the whole pipeline is behaviorally identical to
/// `--sat-no-subst-auto` (verified byte-identical `--stats` behavioral counters
/// on 43fbacb2, fix-default vs AUTO=0).
///
/// WHY A FORMULA-density cap: the probe's own 0.05 EQUIVALENCE-density gate
/// (probe equivalences / active vars) does NOT correlate with formula
/// density — measured on 43fbacb2 (48K clauses, formula density 60.3): the
/// probe found 400 equivalences over 800 active vars (equivalence density
/// 0.50, `collapse_worthy=TRUE`), armed the collapse machinery, and lost a
/// 4.2s SAT (recovered, model-verified + kissat-confirmed, with AUTO off).
///
/// WHY EARLY (inside compute_preprocess_policy, not at the probe block): a
/// late disarm placed after the policy reads `congruence.enabled` leaves
/// `skip_congruence == false`, which flips the level-0 GC to the full
/// `collect_level0_garbage` path instead of AUTO=0's lightweight one — the
/// run is then NOT equivalent to the kill-switch and the recovery does not
/// reproduce (measured counter divergence on the rejected first attempt).
///
/// WHY THE VALUE 20 (reuse of `PREPROCESS_BVE_SKIP_DENSITY`): winner
/// signature from the wf_55735963 default-on measurement — all 7 sparse
/// AUTO flips (df813fe7, 6f354fbe, d88a8a62, 0205e2df, f5c12b1e, 70da0b78,
/// 96dea345) live at formula density 2.3–9.3, more than 2x below the cap;
/// every measured dense casualty is at density >= 60.3 (43fbacb2 60.3,
/// ccc66f69 134, 0ec8c5e9 359, e7ee736c 2167), at least 3x above it. The
/// cap therefore costs the flips nothing by construction while removing
/// the probe from the whole dense band (e.g. the measured 605ms
/// probe+gate-extraction tax on e7ee736c, 1.04M clauses).
///
/// ACCEPTED-AS-COST (do not chase with wider guards): ccc66f69 (density
/// 134), e7ee736c (2167) and ddf96204 (370) stay lost at the 120s budget —
/// attribution showed ALL kill-switch arms (including AUTO=0) lose them;
/// they are 1.1–5.3s-margin timeout-edge casualties of the husk L0-GC/
/// subsume + congruence SAT-side soundness fixes (bd67a48a), which must not
/// be reverted. This cap still removes the dense probe tax, so they may
/// return stochastically.
///
/// ACCEPTED-AS-TRADE (remeasure3 SAT-churn attribution, 2026-07, main
/// 8b40f19a — do NOT revert and do NOT add a finer dense-giant guard):
/// this disarm is the attributed cause of losing 1b880681 (19.6M clauses,
/// parsed density 351.6, historically SAT@97.6s → UNKNOWN@120s).
/// Differential: default and --sat-no-subst-auto both UNKNOWN@120s;
/// --sat-no-subst-auto=1 (uncapped, no disarm) recovers SAT@100.4s
/// (model-verified over all 19.6M clauses, kissat-agreed). Mechanism: the
/// pre-disarm armed-flag leak bought 2.9s of inprocessing decompose
/// (inproc_decompose_ms 2873, decomp_subst 62) whose 62 substitutions
/// steer that instance's SAT trajectory. This is the exact mirror of
/// 0ec8c5e9 (21.2M clauses, density 359, ~2.8s decompose) which the SAME
/// disarm RECOVERED (+46s margin) and which is a regression-floor member:
/// two near-identical dense giants want opposite settings, no clean
/// predicate separates densities 351.6 vs 359, and any finer guard is
/// overfitting to one instance. The trade is conserved (+0ec8c5e9 /
/// −1b880681), not a net regression. If both are ever wanted, the
/// candidate is a SINGLE bounded (~3s-cap) decompose re-run on disarmed
/// dense giants — a new lever needing its own A/B, not a guard tweak here.
///
/// INPUT CONTRACT — PARSED density only: the argument must be
/// `num_clauses / num_vars` on the PARSED counts, NOT the policy's
/// `formula_density` (which divides by trail-adjusted ACTIVE vars). The
/// flip/casualty band above is defined on parsed counts; instances that
/// ship many unit clauses (6f354fbe: 28,984 units) have an active density
/// far above their parsed density (~24 vs 9.34) and would be mis-disarmed
/// — measured to LOSE that sentinel flip (UNKNOWN@120s vs main
/// UNSAT@113.8s). See `auto_probe_dense_cap_must_see_parsed_density_not_active`.
///
/// Applies ONLY when `cold.subst_auto_capped` is set (DEFAULT-ON path);
/// explicit `--sat-no-subst-auto=1` keeps the historical uncapped semantics.
pub(super) fn auto_probe_skip_dense(parsed_formula_density: f64) -> bool {
    parsed_formula_density > PREPROCESS_BVE_SKIP_DENSITY
}

/// Giant-formula bail for the two probe-path decompose RE-RUN sites in
/// `inprocessing_schedule.rs` (HTR `produced_binary` and
/// `probe_found_failed`) — the second half of the 2026-07-11 dense-band
/// regression fix. Pure predicate (env-free, unit-tested below): `true`
/// means the re-run site must NOT fire this round.
///
/// MECHANISM (0ec8c5e9, 21.2M clauses, density 359, 46s-margin SAT lost):
/// AUTO arms `features.decompose/congruence` at config time; above the AUTO
/// probe caps (2M vars / 8M clauses) the preprocess probe block never
/// executes, and its not-worthy bail — the ONLY place AUTO disarms — never
/// fires. The armed flags then leak into inprocessing, where these two
/// re-run sites are gated only by `should_decompose()` (enabled + backoff)
/// and BYPASS `skip_congruence_inproc`: measured 2,760ms of decompose (4
/// runs, 2 yielding substitution passes) on the 21M-clause arena. The
/// early dense disarm (guard 1) already covers every MEASURED giant (all
/// are dense); this bail is the defense-in-depth for a sparse >8M-clause
/// giant, and hard-stops O(total_literals) re-runs regardless.
///
/// WHY NOT plain `skip_congruence_inproc` at those sites: that predicate
/// also fires on vars > 200K / clauses > 3M / dense-inproc shapes — which
/// includes the df813fe7 flip (521K vars, 1.31M clauses). And why NOT a
/// global fail-closed disarm of armed-but-unprobed flags: that was
/// measured to LOSE the 6f354fbe flip (density 9.3 — its UNSAT depends on
/// the armed flags leaking into inprocessing on its skip path). This bail
/// uses ONLY the AUTO clause cap (8M): every flip is <= 1.31M clauses
/// (>6x headroom), so below-cap instances keep today's behavior
/// bit-for-bit, leak included.
///
/// Applies ONLY when `subst_auto_capped` (DEFAULT-ON path); explicit
/// `--sat-no-subst-auto=1` keeps the historical uncapped semantics, and
/// non-Default variants / Custom congruence profiles (capped == false)
/// are untouched.
///
/// EXONERATED for the remeasure3 giant SAT losses (2026-07, main 8b40f19a):
/// this bail was the prime suspect for 1b880681 (SAT@97.6s → UNKNOWN) but
/// is structurally MOOT on every measured giant — they are all dense
/// (parsed density 351.6–370), so the early dense disarm fires first in
/// compute_preprocess_policy, `decompose.enabled` is already false, and the
/// two re-run sites this predicate guards never fire regardless. The
/// operative change on 1b880681 is the dense disarm itself (see
/// auto_probe_skip_dense, ACCEPTED-AS-TRADE). Keep this bail exactly as-is:
/// it remains the defense-in-depth for a SPARSE (density <= 20) >8M-clause
/// giant, which the dense disarm by definition does not cover.
///
/// GIANT-3M NOTE (2026-07): keyed to the DECOUPLED
/// `AUTO_DECOMPOSE_RERUN_MAX_CLAUSES` (8M, the historical value) rather
/// than the probe caps, so the non-proof giant-band probe raise
/// (`AUTO_CONGRUENCE_GIANT_MAX_CLAUSES` = 10M) does not widen this drag
/// bound — the bail's O(total_literals) economics argument is about arena
/// size, not probe eligibility. Post-collapse residuals of the giant-band
/// flips (~4.5M active) sit below it, so their re-runs are unaffected.
pub(in crate::solver) fn auto_capped_giant_skips_decompose_rerun(
    subst_auto_capped: bool,
    active_clauses: usize,
) -> bool {
    subst_auto_capped && active_clauses > AUTO_DECOMPOSE_RERUN_MAX_CLAUSES
}

#[derive(Debug, Clone, Copy)]
pub(super) struct PreprocessPolicy {
    pub(super) skip_gate_dependent_passes: bool,
    pub(super) skip_expensive_preprocessing_passes: bool,
    pub(super) skip_dense_formula: bool,
    pub(super) skip_congruence: bool,
    pub(super) preprocessing_quick_mode: bool,
    pub(super) formula_density: f64,
}

impl Solver {
    pub(super) fn compute_preprocess_policy(&mut self) -> PreprocessPolicy {
        let num_clauses = self.arena.num_clauses();
        let active_clauses = self.arena.active_clause_count();
        let active_vars_est = self.num_vars.saturating_sub(self.trail.len());
        let formula_density = PreprocessPolicy::formula_density(active_clauses, active_vars_est);
        // EARLY dense disarm of the DEFAULT-ON AUTO collapse arming
        // (2026-07-11 dense-band regression fix — see auto_probe_skip_dense
        // for the full measurement). Placement is load-bearing: it must run
        // BEFORE this function reads `congruence.enabled` (skip_congruence)
        // and `cold.subst_auto_collapse` (the raised AUTO caps) so that a
        // dense instance's entire pipeline — lightweight L0-GC path,
        // preprocess probe block, want_fixpoint, and every inprocessing
        // decompose/congruence gate — is behaviorally identical to
        // --sat-no-subst-auto. A later disarm leaves skip_congruence false
        // and diverges (the rejected first attempt). Scoped to the
        // DEFAULT-ON path (`cold.subst_auto_capped`): explicit
        // --sat-no-subst-auto=1 keeps the historical uncapped semantics.
        //
        // The predicate is fed the PARSED density (num_clauses / num_vars),
        // NOT `formula_density` (active-vars based): 6f354fbe parses 28,984
        // unit clauses, so its trail-adjusted density at policy time is ~24
        // (> 20) while its parsed density is 9.3 — the attribution's
        // flip/casualty band (flips 2.5–9.3, casualties >= 60.3) is defined
        // on PARSED counts. Feeding the active density disarmed the
        // sentinel flip 6f354fbe and lost it (measured UNKNOWN@120s vs main
        // UNSAT@113.8s, same machine/load; probe line absent + preprocess
        // 533ms shorter confirmed the mis-fire).
        let parsed_formula_density = if self.num_vars > 0 {
            num_clauses as f64 / self.num_vars as f64
        } else {
            0.0
        };
        if self.cold.subst_auto_capped && auto_probe_skip_dense(parsed_formula_density) {
            self.inproc_ctrl.decompose.enabled = false;
            self.inproc_ctrl.congruence.enabled = false;
            self.cold.subst_auto_collapse = false;
        }
        let skip_dense_formula =
            PreprocessPolicy::skip_dense_formula(active_clauses, formula_density);
        // Dense-skip elimination lift (2026-07, kill-switch
        // AY_AB_DENSE_SKIP_LIFT=0): the expensive-pass gate uses the
        // raised-band elimination variant; the `skip_dense_formula` policy
        // field (decompose/cleanup gates) keeps the original predicate. See
        // skip_dense_formula_elim for the measurement.
        let skip_expensive_preprocessing_passes = self.num_vars > PREPROCESS_EXPENSIVE_MAX_VARS
            || num_clauses > PREPROCESS_EXPENSIVE_MAX_CLAUSES
            || PreprocessPolicy::skip_dense_formula_elim(active_clauses, formula_density);

        // Congruence size caps (#15, 2026-07-03): the full-400 showed 3 of the
        // winner-fast UNSAT losses (07cea7 783k vars, df813 521k, 9d7caee
        // 1.7M) are huge ternary-dominant substitution instances the winner
        // (Kissat, no such cap) cracks in 3-8s but AY skips congruence on. The
        // clause-driven XOR extraction is now cheap (15ms/70da), so the
        // 200k-var / 3M-clause caps are overly conservative. --sat-no-subst-auto
        // raises them (probe is affordable, and its density gate bails cheaply
        // if the big instance is NOT substitution-heavy) — but keep an upper
        // bound so truly enormous formulas still skip. Default ON since
        // 2026-07-10 (wf_55735963); the flag is armed per resolved config by
        // VariantConfig::apply_to_solver (Default DIMACS variant only,
        // kill-switch --sat-no-subst-auto).
        let auto_collapse = self.cold.subst_auto_collapse;
        // Giant-band raise (giant-3M fix, 2026-07 — see
        // AUTO_CONGRUENCE_GIANT_MAX_VARS): NON-PROOF default-path solves get
        // the 4M/10M probe band (5ceb95f5 SAT@62.0s, ac388757 SAT@58.6s,
        // models validated); proof solves and explicit --sat-no-subst-auto=1
        // keep the historical 2M/8M band bit-for-bit (cold.subst_auto_giant
        // is armed only on the capped non-proof path). Kill-switch
        // AY_AB_SUBST_AUTO_GIANT=0 restores 2M/8M exactly.
        let auto_giant = auto_collapse && self.cold.subst_auto_giant;
        let cong_max_vars = if auto_giant {
            AUTO_CONGRUENCE_GIANT_MAX_VARS
        } else if auto_collapse {
            AUTO_CONGRUENCE_MAX_VARS
        } else {
            PREPROCESS_EXPENSIVE_MAX_VARS
        };
        let cong_max_clauses = if auto_giant {
            AUTO_CONGRUENCE_GIANT_MAX_CLAUSES
        } else if auto_collapse {
            AUTO_CONGRUENCE_MAX_CLAUSES
        } else {
            CONGRUENCE_MAX_CLAUSES
        };
        PreprocessPolicy {
            skip_gate_dependent_passes: self.is_uniform_nonbinary_irredundant_formula(),
            skip_expensive_preprocessing_passes,
            skip_dense_formula,
            skip_congruence: self.num_vars > cong_max_vars
                || num_clauses > cong_max_clauses
                || !self.inproc_ctrl.congruence.enabled,
            preprocessing_quick_mode: self.preprocessing_quick_mode,
            formula_density,
        }
    }
}

/// Pure band predicate for the giant-3M raised probe band (unit-tested
/// below): true iff the PARSED counts are ABOVE the historical 2M/8M AUTO
/// caps but WITHIN the raised 4M/10M giant caps. Everything at or below the
/// historical caps keeps today's behavior bit-for-bit (budget included);
/// everything above the giant caps stays skipped as before.
pub(super) fn auto_giant_band_counts(num_vars: usize, num_clauses: usize) -> bool {
    (num_vars > AUTO_CONGRUENCE_MAX_VARS || num_clauses > AUTO_CONGRUENCE_MAX_CLAUSES)
        && num_vars <= AUTO_CONGRUENCE_GIANT_MAX_VARS
        && num_clauses <= AUTO_CONGRUENCE_GIANT_MAX_CLAUSES
}

impl Solver {
    /// Preprocess-budget arm of the giant-3M fix (see
    /// `AUTO_GIANT_PREPROCESS_BUDGET_SECS`): true iff this solve is an
    /// AUTO-armed, giant-band-armed (non-proof, default-path,
    /// AY_AB_SUBST_AUTO_GIANT not =0) instance whose PARSED counts sit in
    /// the raised band and which the EARLY dense disarm will NOT disarm.
    /// Without the raised budget the 2s `Large` class budget is consumed by
    /// the full level-0 GC alone (~2.1s at 8.5M clauses) and probe entry is
    /// a load-dependent coin flip.
    ///
    /// The dense check mirrors `auto_probe_skip_dense` on the same PARSED
    /// density that compute_preprocess_policy feeds it, so a dense giant
    /// (which the policy disarms before the caps are consulted) keeps its
    /// class budget bit-for-bit instead of receiving 12s of preprocessing
    /// it can no longer use on the probe.
    pub(super) fn auto_giant_preprocess_budget_active(&self) -> bool {
        if !(self.cold.subst_auto_giant && self.cold.subst_auto_collapse) {
            return false;
        }
        if !(self.inproc_ctrl.congruence.enabled && self.inproc_ctrl.decompose.enabled) {
            return false;
        }
        let num_clauses = self.arena.num_clauses();
        if !auto_giant_band_counts(self.num_vars, num_clauses) {
            return false;
        }
        let parsed_formula_density = if self.num_vars > 0 {
            num_clauses as f64 / self.num_vars as f64
        } else {
            0.0
        };
        !(self.cold.subst_auto_capped && auto_probe_skip_dense(parsed_formula_density))
    }
}

impl PreprocessPolicy {
    pub(super) fn budget_secs_for_counts(num_vars: usize, num_clauses: usize) -> u64 {
        match FormulaClass::classify(num_vars, num_clauses) {
            FormulaClass::Small => 2,
            // CaDiCaL spends 3-5s preprocessing medium formulas (#8448).
            // A 2s budget truncates BVE before it can cascade on structured
            // medium instances, so keep the existing 5s budget.
            FormulaClass::Medium => 5,
            // (#8448) Reduced from 5 to 2. The 7/23 SAT-COMP score was
            // achieved with a 2s budget for Large formulas.
            FormulaClass::Large => 2,
        }
    }

    fn formula_density(active_clauses: usize, active_vars_est: usize) -> f64 {
        if active_vars_est > 0 {
            active_clauses as f64 / active_vars_est as f64
        } else {
            0.0
        }
    }

    pub(super) fn skip_dense_formula(active_clauses: usize, formula_density: f64) -> bool {
        (active_clauses > PREPROCESS_BVE_SKIP_CLAUSE_THRESHOLD
            && formula_density > PREPROCESS_BVE_SKIP_DENSITY)
            || formula_density > BVE_HIGH_DENSITY_SKIP
    }

    /// Dense-skip elimination lift (2026-07 d421913d root-cause fix,
    /// DEFAULT ON, kill-switch `AY_AB_DENSE_SKIP_LIFT=0`): raised-band
    /// variant of [`Self::skip_dense_formula`] for the ELIMINATION-side
    /// gates only — preprocess `skip_expensive_preprocessing_passes`,
    /// inproc `skip_bve_dense` / `skip_expensive_equivalence_passes` /
    /// `skip_subsume_inproc`. The clause arm is raised from the 2M
    /// [`PREPROCESS_BVE_SKIP_CLAUSE_THRESHOLD`] to the 3M
    /// [`PREPROCESS_EXPENSIVE_MAX_CLAUSES`] (the general expensive-pass
    /// clause cap), unlocking the (2M,3M] clauses x (20,50] density band
    /// for factor/BVE/HTR/subsume/probe. The density-only arm (>50) is
    /// unchanged. Decompose/congruence gates keep the ORIGINAL predicate
    /// everywhere (the #8448 dense-decompose false-UNSAT guard and the
    /// AUTO dense probe disarm are untouched).
    ///
    /// MEASUREMENT (worktree wf_58ce34a3, serial same-binary A/B on
    /// d421913d — 60,746 vars / 2,435,854 clauses, density 40.1, the sole
    /// main2025 instance tripping the 2M clause arm while otherwise
    /// in-band): lift ON = s UNSATISFIABLE @~64s and @78.8s (two runs),
    /// 165,641 conflicts, factor_count=6,039 (kissat parity: kissat
    /// factors 6,705 vars on this instance, UNSAT @53.5s); lift OFF
    /// control = UNKNOWN@120s, 384,323 conflicts. Certificate: 74MB DRAT
    /// -> dpr-trim `s VERIFIED` -> cake_lpr `s VERIFIED UNSAT`,
    /// kissat-agreeing. Floor exposure zero by band arithmetic: no
    /// regression-floor hash sits in (2M,3M] x (20,50] (6f354fbe 448K
    /// clauses; 43fbacb2/0ec8c5e9 fire the unchanged >50 density arm;
    /// the rest are density < 20 or > 3M clauses).
    pub(super) fn skip_dense_formula_elim(active_clauses: usize, formula_density: f64) -> bool {
        if !dense_skip_lift_enabled() {
            return Self::skip_dense_formula(active_clauses, formula_density);
        }
        Self::skip_dense_formula_elim_raised(active_clauses, formula_density)
    }

    /// Pure raised-band predicate for the dense-skip elimination lift
    /// (env-free, unit-tested below): the 3M clause arm plus the unchanged
    /// >50 density-only arm.
    pub(super) fn skip_dense_formula_elim_raised(
        active_clauses: usize,
        formula_density: f64,
    ) -> bool {
        (active_clauses > PREPROCESS_EXPENSIVE_MAX_CLAUSES
            && formula_density > PREPROCESS_BVE_SKIP_DENSITY)
            || formula_density > BVE_HIGH_DENSITY_SKIP
    }
}

/// Kill-switch for the dense-skip elimination lift (see
/// [`PreprocessPolicy::skip_dense_formula_elim`]). DEFAULT ON;
/// `AY_AB_DENSE_SKIP_LIFT=0` restores the original 2M-clause-arm predicate
/// on all four elimination-side gates byte-for-byte. Cached OnceLock per
/// the #8506 no-per-call-syscall convention.
pub(in crate::solver) fn dense_skip_lift_enabled() -> bool {
    // B26: CLI-owned opt-out (--sat-no-dense-skip-lift); env retired.
    !ay_core::sat_ab_switches().no_dense_skip_lift
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn preprocess_policy_thresholds_match_existing_gates() {
        assert_eq!(PreprocessPolicy::budget_secs_for_counts(9_999, 99_999), 2);
        assert_eq!(PreprocessPolicy::budget_secs_for_counts(10_000, 100_000), 5);
        assert_eq!(
            PreprocessPolicy::budget_secs_for_counts(PREPROCESS_EXPENSIVE_MAX_VARS, 100_000),
            2
        );
        assert_eq!(
            PreprocessPolicy::budget_secs_for_counts(10_000, PREPROCESS_EXPENSIVE_MAX_CLAUSES),
            2
        );

        assert!(!PreprocessPolicy::skip_dense_formula(
            PREPROCESS_BVE_SKIP_CLAUSE_THRESHOLD,
            PREPROCESS_BVE_SKIP_DENSITY + 0.1,
        ));
        assert!(PreprocessPolicy::skip_dense_formula(
            PREPROCESS_BVE_SKIP_CLAUSE_THRESHOLD + 1,
            PREPROCESS_BVE_SKIP_DENSITY + 0.1,
        ));
        assert!(PreprocessPolicy::skip_dense_formula(
            1,
            BVE_HIGH_DENSITY_SKIP + 0.1,
        ));
    }

    #[test]
    fn dense_skip_elim_lift_unlocks_exactly_the_2m_to_3m_band() {
        // The lifted band is (2M, 3M] clauses x (20, 50] density: the
        // d421913d target (2.44M clauses, density 40.1) must be admitted.
        assert!(!PreprocessPolicy::skip_dense_formula_elim_raised(
            2_435_854, 40.1
        ));
        // The original predicate skips it (the pre-fix behavior the
        // kill-switch restores).
        assert!(PreprocessPolicy::skip_dense_formula(2_435_854, 40.1));
        // Above the raised 3M clause arm: still skipped.
        assert!(PreprocessPolicy::skip_dense_formula_elim_raised(
            PREPROCESS_EXPENSIVE_MAX_CLAUSES + 1,
            PREPROCESS_BVE_SKIP_DENSITY + 0.1,
        ));
        // At the raised arm boundary: admitted (matches the >3M general
        // expensive-pass cap convention).
        assert!(!PreprocessPolicy::skip_dense_formula_elim_raised(
            PREPROCESS_EXPENSIVE_MAX_CLAUSES,
            PREPROCESS_BVE_SKIP_DENSITY + 0.1,
        ));
        // The density-only arm (>50) is unchanged: 43fbacb2 (density 60.3)
        // and 0ec8c5e9 (density 359) keep firing it regardless of clause
        // count.
        assert!(PreprocessPolicy::skip_dense_formula_elim_raised(1, 60.3));
        assert!(PreprocessPolicy::skip_dense_formula_elim_raised(
            1,
            BVE_HIGH_DENSITY_SKIP + 0.1,
        ));
        // Below-density formulas stay admitted in both variants.
        assert!(!PreprocessPolicy::skip_dense_formula_elim_raised(
            2_500_000,
            PREPROCESS_BVE_SKIP_DENSITY,
        ));
    }

    #[test]
    fn dense_skip_elim_lift_is_inert_outside_the_lifted_band() {
        // Structural G5: the raised predicate agrees with the original
        // everywhere EXCEPT (2M, 3M] clauses x (20, 50] density, so the
        // kill-switch can only change behavior inside that band. Grid over
        // representative points on both sides of every arm boundary.
        let clause_points = [
            0,
            1,
            448_000,   // 6f354fbe
            1_310_000, // df813fe7
            PREPROCESS_BVE_SKIP_CLAUSE_THRESHOLD,
            PREPROCESS_BVE_SKIP_CLAUSE_THRESHOLD + 1,
            2_435_854, // d421913d target
            PREPROCESS_EXPENSIVE_MAX_CLAUSES,
            PREPROCESS_EXPENSIVE_MAX_CLAUSES + 1,
            8_000_000,
            21_161_364, // 0ec8c5e9
        ];
        let density_points = [
            0.0,
            2.5,
            PREPROCESS_BVE_SKIP_DENSITY,
            PREPROCESS_BVE_SKIP_DENSITY + 0.1,
            40.1, // d421913d target
            BVE_HIGH_DENSITY_SKIP,
            BVE_HIGH_DENSITY_SKIP + 0.1,
            60.3,  // 43fbacb2
            359.0, // 0ec8c5e9
        ];
        for &c in &clause_points {
            for &d in &density_points {
                let in_lifted_band = c > PREPROCESS_BVE_SKIP_CLAUSE_THRESHOLD
                    && c <= PREPROCESS_EXPENSIVE_MAX_CLAUSES
                    && d > PREPROCESS_BVE_SKIP_DENSITY
                    && d <= BVE_HIGH_DENSITY_SKIP;
                let orig = PreprocessPolicy::skip_dense_formula(c, d);
                let raised = PreprocessPolicy::skip_dense_formula_elim_raised(c, d);
                if in_lifted_band {
                    assert!(orig && !raised, "band point ({c}, {d}) must be unlocked");
                } else {
                    assert_eq!(orig, raised, "outside-band point ({c}, {d}) must be inert");
                }
            }
        }
    }

    #[test]
    fn auto_probe_dense_cap_admits_the_flip_band() {
        // Winner signature (wf_55735963 measurement): all 7 sparse AUTO
        // flips live at formula density 2.3–9.3. The cap must admit the
        // whole band with headroom — losing any flip means the cap is wrong.
        for density in [2.3, 5.0, 9.3, 15.0] {
            assert!(
                !auto_probe_skip_dense(density),
                "flip-band density {density} must keep the AUTO probe"
            );
        }
        // Exactly at the cap still admits (strict >, matching the
        // skip_dense_formula comparison convention).
        assert!(!auto_probe_skip_dense(PREPROCESS_BVE_SKIP_DENSITY));
    }

    #[test]
    fn auto_probe_dense_cap_must_see_parsed_density_not_active() {
        // Regression pin for the sentinel mis-fire found during gate G3:
        // 6f354fbe parses 448,719 clauses over 48,032 vars (density 9.34)
        // but ships 28,984 UNIT clauses, so the policy's trail-adjusted
        // active density at compute_preprocess_policy time is ~24 (> 20).
        // Feeding the ACTIVE density disarmed the armed-but-unprobed leak
        // this flip depends on and LOST it (UNKNOWN@120s vs main
        // UNSAT@113.8s, same machine/load). The disarm call site MUST feed
        // the PARSED density — the band (flips 2.5–9.3, casualties >= 60.3)
        // is defined on parsed counts.
        let parsed = 448_719f64 / 48_032f64; // 9.34
        let active_at_policy_time = 448_719f64 / 18_594f64; // ~24.1
        assert!(!auto_probe_skip_dense(parsed), "parsed density must admit");
        assert!(
            auto_probe_skip_dense(active_at_policy_time),
            "sanity: the active density WOULD bail — which is exactly why \
             the call site must not use it"
        );
    }

    #[test]
    fn auto_probe_dense_cap_bails_on_the_measured_casualties() {
        // Certified remeasure2 dense casualties (formula densities measured
        // during attribution): every one must bail.
        for density in [60.3, 134.0, 359.0, 2167.0] {
            assert!(
                auto_probe_skip_dense(density),
                "dense casualty density {density} must bail the AUTO probe"
            );
        }
        // Just above the cap bails.
        assert!(auto_probe_skip_dense(PREPROCESS_BVE_SKIP_DENSITY + 0.1));
    }

    #[test]
    fn auto_giant_rerun_bail_admits_every_flip() {
        // Parsed clause counts of the 7 sparse AUTO flips (the instances the
        // dense-band fix must not touch). Largest is df813fe7 at 1,306,928 —
        // more than 6x below the 8M AUTO cap. Learned-clause accumulation
        // cannot realistically bridge that gap within the 120s budget, and
        // G3 verifies the flips empirically end-to-end.
        for clauses in [
            448_719usize, // 6f354fbe (the sentinel: depends on the leak)
            191_642,      // 70da0b78
            400_494,      // 96dea345
            863_565,      // f5c12b1e
            928_103,      // d88a8a62
            933_756,      // 0205e2df
            1_306_928,    // df813fe7 (521K vars — why plain
                          // skip_congruence_inproc must NOT gate the sites)
        ] {
            assert!(
                !auto_capped_giant_skips_decompose_rerun(true, clauses),
                "flip-sized formula ({clauses} clauses) must keep its decompose re-runs"
            );
        }
        // Exactly at the AUTO cap still admits (strict >, matching the
        // skip_congruence cap comparison convention).
        assert!(!auto_capped_giant_skips_decompose_rerun(
            true,
            AUTO_CONGRUENCE_MAX_CLAUSES
        ));
    }

    #[test]
    fn auto_giant_rerun_bail_fires_on_the_measured_giants() {
        // The armed-but-unprobed giants from the certified remeasure2
        // attribution: 0ec8c5e9 (21.2M clauses, the recovered casualty) and
        // ddf96204 (23.6M). Both must bail.
        for clauses in [21_161_364usize, 23_590_384] {
            assert!(
                auto_capped_giant_skips_decompose_rerun(true, clauses),
                "giant ({clauses} clauses) must skip the ungated decompose re-runs"
            );
        }
        assert!(auto_capped_giant_skips_decompose_rerun(
            true,
            AUTO_CONGRUENCE_MAX_CLAUSES + 1
        ));
    }

    #[test]
    fn auto_giant_rerun_bail_scoped_to_the_default_on_path() {
        // Explicit --sat-no-subst-auto=1 (capped == false) keeps the historical
        // uncapped semantics even on a 21M-clause giant; same for
        // non-Default variants and Custom congruence profiles.
        assert!(!auto_capped_giant_skips_decompose_rerun(false, 21_161_364));
    }

    #[test]
    fn auto_giant_rerun_bail_decoupled_from_the_raised_probe_band() {
        // Giant-3M fix invariant: the re-run drag bound stays at 8M and must
        // NOT widen to the raised 10M probe cap — a 10M-clause arena still
        // bails even though the probe band now admits it.
        assert!(auto_capped_giant_skips_decompose_rerun(
            true,
            AUTO_CONGRUENCE_GIANT_MAX_CLAUSES
        ));
        // The measured post-collapse residual of the 5ceb95f5 flip (~4.5M
        // active clauses) keeps its inprocessing re-runs.
        assert!(!auto_capped_giant_skips_decompose_rerun(true, 4_503_933));
    }

    #[test]
    fn auto_giant_band_admits_the_measured_flips() {
        // 5ceb95f5 (target, SAT@62.0s) and ac388757 (bonus, SAT@58.6s):
        // both sit just above the historical 2M-var cap, inside 4M/10M.
        assert!(auto_giant_band_counts(3_107_244, 8_545_762));
        assert!(auto_giant_band_counts(3_420_000, 9_200_000));
    }

    #[test]
    fn auto_giant_band_excludes_below_cap_and_beyond_cap_instances() {
        // Below the historical caps: NOT in the raised band — those solves
        // (every regression-floor member included; largest flip df813fe7 is
        // 521K vars / 1.31M clauses, and 9d7caee5 1.69M / 5.96M) keep their
        // class budget and 2M/8M probe caps bit-for-bit.
        assert!(!auto_giant_band_counts(521_000, 1_310_000));
        assert!(!auto_giant_band_counts(1_690_000, 5_960_000));
        assert!(!auto_giant_band_counts(
            AUTO_CONGRUENCE_MAX_VARS,
            AUTO_CONGRUENCE_MAX_CLAUSES
        ));
        // Beyond the giant caps: the SAT giant controls (4d6e18e5 7.3M/40.7M,
        // 00fd8ac9 23.4M/63M) and the dense casualties (0ec8c5e9 21.2M
        // clauses) stay excluded by construction.
        assert!(!auto_giant_band_counts(7_300_000, 40_700_000));
        assert!(!auto_giant_band_counts(23_400_000, 63_000_000));
        assert!(!auto_giant_band_counts(1_000_000, 21_161_364));
        // Strict boundary convention matches skip_congruence (> to exclude,
        // <= to admit): one past the old cap enters, the new cap itself is
        // admitted, one past the new cap leaves.
        assert!(auto_giant_band_counts(AUTO_CONGRUENCE_MAX_VARS + 1, 1));
        assert!(auto_giant_band_counts(
            AUTO_CONGRUENCE_GIANT_MAX_VARS,
            AUTO_CONGRUENCE_GIANT_MAX_CLAUSES
        ));
        assert!(!auto_giant_band_counts(
            AUTO_CONGRUENCE_GIANT_MAX_VARS + 1,
            1
        ));
        assert!(!auto_giant_band_counts(
            1,
            AUTO_CONGRUENCE_GIANT_MAX_CLAUSES + 1
        ));
    }

    #[test]
    fn bve_post_collapse_predicate_off_is_inert() {
        // Knob OFF => never reopens, regardless of how favorable the counts are.
        assert!(!bve_post_collapse_reopens(
            false,
            PREPROCESS_EXPENSIVE_MAX_VARS + 1,
            1,
            PREPROCESS_EXPENSIVE_MAX_VARS,
            BVE_POST_COLLAPSE_MAX_VARS,
        ));
    }

    #[test]
    fn bve_post_collapse_predicate_cap_edges() {
        let original = 723_395; // ebbda8d9-class original count
        let collapsed = 199_888;
        // Exactly at the cap: opens.
        assert!(bve_post_collapse_reopens(
            true,
            original,
            BVE_POST_COLLAPSE_MAX_VARS,
            collapsed,
            BVE_POST_COLLAPSE_MAX_VARS,
        ));
        // One above the cap: stays closed.
        assert!(!bve_post_collapse_reopens(
            true,
            original,
            BVE_POST_COLLAPSE_MAX_VARS + 1,
            collapsed,
            BVE_POST_COLLAPSE_MAX_VARS,
        ));
        // Env-tuned cap is honored (raised cap admits the same residual).
        assert!(bve_post_collapse_reopens(
            true,
            original,
            BVE_POST_COLLAPSE_MAX_VARS + 1,
            collapsed,
            BVE_POST_COLLAPSE_MAX_VARS + 1,
        ));
    }

    #[test]
    fn bve_post_collapse_predicate_requires_a_collapse() {
        // Collapse merged nothing => no effect, even if fixed vars alone
        // brought the active count under the cap.
        assert!(!bve_post_collapse_reopens(
            true,
            PREPROCESS_EXPENSIVE_MAX_VARS + 1,
            PREPROCESS_EXPENSIVE_MAX_VARS,
            0,
            BVE_POST_COLLAPSE_MAX_VARS,
        ));
    }

    #[test]
    fn bve_post_collapse_predicate_only_opens_above_cap_cases() {
        // In-band originals (<= PREPROCESS_EXPENSIVE_MAX_VARS) are never
        // touched: the re-derivation only OPENS above-cap cases, it can never
        // close (or otherwise alter) in-band ones.
        for original in [1, 1_000, PREPROCESS_EXPENSIVE_MAX_VARS] {
            assert!(!bve_post_collapse_reopens(
                true,
                original,
                original / 2,
                original / 2,
                BVE_POST_COLLAPSE_MAX_VARS,
            ));
        }
        // Sanity: the same counts one variable above the gate DO open.
        assert!(bve_post_collapse_reopens(
            true,
            PREPROCESS_EXPENSIVE_MAX_VARS + 1,
            PREPROCESS_EXPENSIVE_MAX_VARS / 2,
            1,
            BVE_POST_COLLAPSE_MAX_VARS,
        ));
    }

    #[test]
    fn bve_giant_raw_qualifies_requires_route_and_no_collapse() {
        // 9d7caee5 shape at qualification time: 1.69M vars, 5.96M clauses,
        // density 3.5, zero collapse (AUTO probe equivalence density 0).
        let (clauses, vars) = (5_959_122usize, 1_694_511usize);
        assert!(bve_giant_raw_qualifies(true, 0, clauses, vars));
        // Route flag off => never qualifies.
        assert!(!bve_giant_raw_qualifies(false, 0, clauses, vars));
        // ANY collapse => the post-collapse lever owns it (disjoint by
        // construction: 07cea7a6 collapses 275,256; ebbda8d9 ~201K).
        assert!(!bve_giant_raw_qualifies(true, 1, clauses, vars));
        assert!(!bve_giant_raw_qualifies(true, 275_256, clauses, vars));
    }

    #[test]
    fn bve_giant_raw_qualifies_rechecks_dense_skip_live() {
        // A formula that densified past the dense-skip guard after the
        // header-derived route flag was set must be refused: >2M active
        // clauses at density >20 (0ec8c5e9-like shape: 21.2M clauses over
        // 59K vars, density 359).
        assert!(!bve_giant_raw_qualifies(true, 0, 21_161_364, 58_983));
        // Density just above the high-density skip is refused even when
        // small.
        assert!(!bve_giant_raw_qualifies(true, 0, 51_000, 1_000));
        // Zero active vars degenerate case: refused via density 0 path?
        // density computes 0.0 and skip_dense_formula(clauses, 0.0) admits
        // only when clauses are under the 2M threshold — a giant with no
        // active vars left has nothing to eliminate but must not panic.
        assert!(bve_giant_raw_qualifies(true, 0, 0, 0));
    }

    #[test]
    fn bve_post_collapse_env_default_is_on() {
        // Default flipped ON 2026-07-10 (wf_55735963: +7 UNSAT flips / 0 hard
        // losses on the main2025 scoreboard protocol — see
        // bve_post_collapse_enabled). B34: the kill is CLI-owned
        // (--sat-no-bve-post-collapse), so the default assert is
        // unconditional.
        assert!(
            bve_post_collapse_enabled(),
            "the post-collapse BVE unlock must default ON (wf_55735963 flip)"
        );
        // B3: the accessor is env-free; assert the constant directly.
        assert_eq!(bve_post_collapse_max_vars(), BVE_POST_COLLAPSE_MAX_VARS);
    }

    #[test]
    fn bve_post_factor_predicate_off_is_inert() {
        // Knob OFF => never reopens, regardless of how favorable the collapse.
        assert!(!bve_post_factor_reopens(
            false,
            11_135_080, // f6a085f3 original active clauses
            371_269,    // factored residual
            70_867,     // extension vars created
            PREPROCESS_EXPENSIVE_MAX_CLAUSES,
            BVE_POST_FACTOR_MIN_COLLAPSE_RATIO,
        ));
    }

    #[test]
    fn bve_post_factor_predicate_fires_on_the_f6_collapse() {
        // The measured f6a085f3 collapse (deep drain): 11.1M active clauses →
        // 371,269, 70,867 extension vars, ratio ~30. Must arm.
        assert!(bve_post_factor_reopens(
            true,
            11_135_080,
            371_269,
            70_867,
            PREPROCESS_EXPENSIVE_MAX_CLAUSES,
            BVE_POST_FACTOR_MIN_COLLAPSE_RATIO,
        ));
    }

    #[test]
    fn bve_post_factor_predicate_only_opens_above_cap_cases() {
        // In-band originals (<= PREPROCESS_EXPENSIVE_MAX_CLAUSES) are never
        // touched: the reopen only OPENS above-cap cases. Below/at the cap the
        // ORIGINAL policy already ran BVE, so re-derivation must be a no-op.
        for original in [1, 1_000_000, PREPROCESS_EXPENSIVE_MAX_CLAUSES] {
            assert!(!bve_post_factor_reopens(
                true,
                original,
                original / 100,
                50_000,
                PREPROCESS_EXPENSIVE_MAX_CLAUSES,
                BVE_POST_FACTOR_MIN_COLLAPSE_RATIO,
            ));
        }
        // One clause above the cap DOES open (same counts otherwise).
        assert!(bve_post_factor_reopens(
            true,
            PREPROCESS_EXPENSIVE_MAX_CLAUSES + 1,
            (PREPROCESS_EXPENSIVE_MAX_CLAUSES + 1) / 100,
            50_000,
            PREPROCESS_EXPENSIVE_MAX_CLAUSES,
            BVE_POST_FACTOR_MIN_COLLAPSE_RATIO,
        ));
    }

    #[test]
    fn bve_post_factor_predicate_requires_factoring_and_residual_and_ratio() {
        let cap = PREPROCESS_EXPENSIVE_MAX_CLAUSES;
        let ratio = BVE_POST_FACTOR_MIN_COLLAPSE_RATIO;
        // Factoring did nothing (factored_vars == 0) => inert even with a huge
        // apparent collapse.
        assert!(!bve_post_factor_reopens(
            true, 11_000_000, 100_000, 0, cap, ratio
        ));
        // Residual still above the cap => stays closed (nothing gained).
        assert!(!bve_post_factor_reopens(
            true,
            11_000_000,
            cap + 1,
            70_000,
            cap,
            ratio,
        ));
        // Small-ratio collapse (just under the ratio floor) => stays closed:
        // residual = original / (ratio - epsilon) is still cap-bounded but the
        // ratio guard rejects it.
        let residual = (cap as f64 / (ratio - 1.0)) as usize; // ratio ~7.0 < 8.0
        assert!(residual <= cap);
        assert!(!bve_post_factor_reopens(
            true,
            cap + 1,
            residual,
            70_000,
            cap,
            ratio,
        ));
        // Exactly at the ratio edge opens (original == ratio * residual), with
        // a residual chosen so original stays above the cap.
        let residual_edge = 400_000usize;
        let original_edge = (ratio * residual_edge as f64) as usize; // 3.2M > cap
        assert!(original_edge > cap);
        assert!(bve_post_factor_reopens(
            true,
            original_edge,
            residual_edge,
            70_000,
            cap,
            ratio,
        ));
    }

    #[test]
    fn bve_post_factor_stays_retired() {
        // B21: the measured-negative lever's env spelling is retired; the
        // reopen must stay compiled-inert until a measurement revives it.
        assert!(!bve_post_factor_enabled());
        // B3: the accessor is env-free; assert the constant directly.
        assert_eq!(
            bve_post_factor_min_collapse_ratio(),
            BVE_POST_FACTOR_MIN_COLLAPSE_RATIO
        );
    }

    #[test]
    fn factor_dense_init_applies_win_loss_boundary() {
        let cap = FACTOR_DENSE_INIT_MAX_CLAUSES;
        let band = FACTOR_DENSE_MIN_DENSITY;

        // Measured WINS (small + dense) get the raise: 46355da (d179, 826K
        // clauses) and a2fe3213 (d171, 1.26M) and 82851650 (d103, 474K).
        assert!(factor_dense_init_applies(true, 179.2, 825_728, cap));
        assert!(factor_dense_init_applies(true, 171.3, 1_262_871, cap));
        assert!(factor_dense_init_applies(true, 103.0, 474_496, cap));

        // Measured LOSS excluded by the residual cap: 0ec8c5e9 (d359, 21M
        // clauses) flipped SAT@88s -> timeout with the raise; the cap keeps it
        // on the baseline 500M path.
        assert!(!factor_dense_init_applies(true, 358.8, 21_161_364, cap));
        // The density-264 cluster (~11M clauses) is likewise excluded.
        assert!(!factor_dense_init_applies(true, 264.8, 11_000_000, cap));

        // Sub-band moderate density excluded regardless of size (43fbacb2 d60).
        assert!(!factor_dense_init_applies(true, 60.4, 48_439, cap));
        assert!(!factor_dense_init_applies(true, band - 0.1, 100, cap));
        // Band edge is inclusive.
        assert!(factor_dense_init_applies(true, band, 100, cap));
        // Clause-cap edge is inclusive.
        assert!(factor_dense_init_applies(true, band, cap, cap));
        assert!(!factor_dense_init_applies(true, band, cap + 1, cap));

        // Kill-switch (enabled == false) never applies, even in-band.
        assert!(!factor_dense_init_applies(false, 179.2, 825_728, cap));
    }

    #[test]
    fn factor_dense_init_env_defaults() {
        assert!(
            factor_dense_init_enabled(),
            "the dense-band first-call factor bonus must default ON \
             (`--sat-no-factor-dense-init` kills it)"
        );
        // B3: the accessors are env-free; assert the constants directly.
        assert_eq!(factor_dense_init_ticks(), FACTOR_DENSE_INIT_TICKS);
        assert_eq!(
            factor_dense_init_max_clauses(),
            FACTOR_DENSE_INIT_MAX_CLAUSES
        );
        // B3: the accessor is env-free; the clamp is the compile-time ceiling.
        assert_eq!(factor_max_effort(), FACTOR_MAX_EFFORT);
    }
}
