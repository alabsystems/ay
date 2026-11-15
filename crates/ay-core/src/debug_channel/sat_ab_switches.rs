// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Process-constant SAT A/B switches installed by the CLI.

use std::sync::OnceLock;

/// SAT-engine A/B opt-outs, CLI-owned (these replace never-set
/// default-on `AY_AB_*`/`AY_SAT_*` kill-switch env vars). Every field
/// defaults FALSE = the shipped engine; each true disables one
/// sound-alternative lane for measurement.
#[derive(Debug, Clone, Copy, Default, PartialEq)]
pub struct SatAbSwitches {
    /// `--sat-no-bve-inst-gate`
    pub no_bve_inst_gate: bool,
    /// `--sat-no-bve-sparse-deep`
    pub no_bve_sparse_deep: bool,
    /// `--sat-no-dense-skip-lift`
    pub no_dense_skip_lift: bool,
    /// `--sat-no-factor-bin-fastpath`
    pub no_factor_bin_fastpath: bool,
    /// `--sat-no-factor-dense`
    pub no_factor_dense: bool,
    /// `--sat-no-factor-dense-init`
    pub no_factor_dense_init: bool,
    /// `--sat-no-lucky`
    pub no_lucky: bool,
    /// `--sat-no-midband-deep-restart`
    pub no_midband_deep_restart: bool,
    /// `--sat-no-orbitope`
    pub no_orbitope: bool,
    /// `--sat-no-orbitope-alo-columns`
    pub no_orbitope_alo_columns: bool,
    /// `--sat-no-symmetry-sr-auxfree`
    pub no_symmetry_sr_auxfree: bool,
    /// `--sat-no-probe-route` (was the AY_AB_PROBE_ROUTE=0 shim)
    pub no_probe_route: bool,
    /// `--sat-no-aggressive-route`
    pub no_aggressive_route: bool,
    /// `--sat-no-bve-sparse`
    pub no_bve_sparse: bool,
    /// `--sat-no-bve-post-collapse`
    pub no_bve_post_collapse: bool,
    /// `--sat-no-subst-auto` (restores the pre-flip opt-in profile)
    pub no_subst_auto: bool,
    /// `--sat-subst-auto-uncapped` (the historical `=1` UNCAPPED
    /// measurement semantics — disarms the dense-band guard rails)
    pub subst_auto_uncapped: bool,
    /// `--sat-no-drat-subst` (force-clamp Decompose+Congruence on DRAT
    /// — the pre-2026-07-09 behavior. The old `=1` force-allow arm was
    /// registry-redundant and is gone.)
    pub no_drat_subst: bool,
    /// `--sat-bve-additive-fastelim` (force the banded additive
    /// fast-elim ON past its band auto decision)
    pub bve_additive_fastelim: bool,
    /// `--sat-no-bve-additive-fastelim` (force it OFF)
    pub no_bve_additive_fastelim: bool,
    /// `--sat-mode-equiticks <true|false>` (was the
    /// `AY_AB_MODE_EQUITICKS` 1/0 tri-state — `Some(true)` forces the
    /// equal-effort stable budgeting ON everywhere, `Some(false)` forces it
    /// OFF, `None` = the shipped default-off resolution)
    pub mode_equiticks: Option<bool>,
    /// `--sat-eqt-progress <N>` (`1` = the default progress-gate
    /// window, `N > 1` sets the window directly; `None`/other = gate inert)
    pub eqt_progress: Option<u64>,
    /// `--sat-congruence-memory-bound` (re-arm the retired congruence
    /// fixpoint memory guard without re-deriving it)
    pub congruence_memory_bound: bool,
    /// `--sat-circuit-equiv-throughput-profile` (opt in to the
    /// multiplier-equivalence throughput profile lane)
    pub circuit_equiv_throughput_profile: bool,
    /// `--sat-signed-symmetry` (opt in to the signed lex-leader route —
    /// measured LOSING on the full 400 at 300s, kept as a sweepable arm)
    pub signed_symmetry: bool,
    /// `--sat-composite-symmetry` (plain lex leaders remain no-proof-only;
    /// `--sat-symmetry-hhw` supplies the supported proof route)
    pub composite_symmetry: bool,
    /// `--sat-symmetry-hhw`
    pub symmetry_hhw: bool,
    /// `--sat-symmetry-fix-and-cut`: Satsuma's fix-and-cut over a Schreier–Sims
    /// chain of the composite generators (WLOG units and orbit binaries) with
    /// the detector's size caps; implies the composite route; no-proof only
    /// until its dominance proof lands (symmetry fixing, step 3).
    pub symmetry_fix_and_cut: bool,
    /// `--sat-bve-sparse-max-vars <n>` (raises/lowers the sparse-BVE
    /// variable ceiling — was `AY_BVE_SPARSE_MAX_VARS`)
    pub bve_sparse_max_vars: Option<usize>,
    /// `--sat-bve-sparse-max-density <f>`
    pub bve_sparse_max_density: Option<f64>,
    /// `--sat-deterministic-inproc <bool>` (tri-state force of the
    /// default-ON deterministic inprocessing budget)
    pub deterministic_inproc: Option<bool>,
    /// `--sat-congruence-parity-trust` (default-off trust arm)
    pub congruence_parity_trust: bool,
    // The dimacs env-lever block becomes typed switches. Opt-in bools
    // default false = the shipped engine; tri-states default None = the
    // compiled default named at the read site.
    /// `--sat-bcp-telemetry` (was `AY_BCP_TELEMETRY`)
    pub bcp_telemetry: bool,
    /// `--sat-bcp-lean` (was `AY_SAT_BCP_LEAN`)
    pub bcp_lean: bool,
    /// `--sat-bcp-disable-trail-lookahead-prefetch` (was `AY_SAT_BCP_DISABLE_TRAIL_LOOKAHEAD_PREFETCH`)
    pub bcp_disable_trail_lookahead_prefetch: bool,
    /// `--sat-bcp-advance-saved-pos` (was `AY_SAT_BCP_ADVANCE_SAVED_POS`)
    pub bcp_advance_saved_pos: bool,
    /// `--sat-bcp-learned-1963-false-saved-pos-reset` (was `AY_SAT_BCP_LEARNED_1963_FALSE_SAVED_POS_RESET`)
    pub bcp_learned_1963_false_saved_pos_reset: bool,
    /// `--sat-bcp-learned-1963-true-tail-relocation` (was `AY_SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION`)
    pub bcp_learned_1963_true_tail_relocation: bool,
    /// `--sat-bcp-learned-618-true-tail-relocation` (was `AY_SAT_BCP_LEARNED_618_TRUE_TAIL_RELOCATION`)
    pub bcp_learned_618_true_tail_relocation: bool,
    /// `--sat-bcp-learned-617-tail-reorder` (was `AY_SAT_BCP_LEARNED_617_TAIL_REORDER`)
    pub bcp_learned_617_tail_reorder: bool,
    /// `--sat-bcp-learned-18-tail-reorder` (was `AY_SAT_BCP_LEARNED_18_TAIL_REORDER`)
    pub bcp_learned_18_tail_reorder: bool,
    /// `--sat-bcp-learned-1963-tail-reorder` (was `AY_SAT_BCP_LEARNED_1963_TAIL_REORDER`)
    pub bcp_learned_1963_tail_reorder: bool,
    /// `--sat-bve-occ-delta-validation` (was `AY_SAT_BVE_OCC_DELTA_VALIDATION`)
    pub bve_occ_delta_validation: bool,
    /// `--sat-bve-occ-saved-state-reuse` (was `AY_SAT_BVE_OCC_SAVED_STATE_REUSE`)
    pub bve_occ_saved_state_reuse: bool,
    /// `--sat-dense-mutex-focused-restart-gate` (was `AY_SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE`)
    pub dense_mutex_focused_restart_gate: bool,
    /// `--sat-dense-clique-mab-branch` (was `AY_SAT_DENSE_CLIQUE_MAB_BRANCH`)
    pub dense_clique_mab_branch: bool,
    /// `--sat-bve-lrat-scout-route` (was `AY_SAT_BVE_LRAT_SCOUT_ROUTE`)
    pub bve_lrat_scout_route: bool,
    /// `--sat-fmla-decompose-lrat-preflight-route` (was `AY_SAT_FMLA_DECOMPOSE_LRAT_PREFLIGHT_ROUTE`)
    pub fmla_decompose_lrat_preflight_route: bool,
    /// `--sat-dense-clique-scout` (was `AY_SAT_DENSE_CLIQUE_SCOUT`)
    pub dense_clique_scout: bool,
    /// `--sat-multiplier-equiv-conservation-scout` (was `AY_SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT`)
    pub multiplier_equiv_conservation_scout: bool,
    /// `--sat-bcp-learned-1963-used5-fsw-saved-pos-reset` (was `AY_SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET`)
    pub bcp_learned_1963_used5_fsw_saved_pos_reset: bool,
    /// `--sat-bcp-learned-1963-fsw-conflict-saved-pos-reset` (was `AY_SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET`)
    pub bcp_learned_1963_fsw_conflict_saved_pos_reset: bool,
    /// `--sat-bcp-learned-no-replacement-saved-pos-update` (was `AY_SAT_BCP_LEARNED_NO_REPLACEMENT_SAVED_POS_UPDATE`)
    pub bcp_learned_no_replacement_saved_pos_update: bool,
    /// `--sat-bcp-learned-1963-fsw-gent-skip` (was `AY_SAT_BCP_LEARNED_1963_FSW_GENT_SKIP`)
    pub bcp_learned_1963_fsw_gent_skip: bool,
    /// `--sat-bcp-learned-no-replacement-scan-pressure` (was `AY_SAT_BCP_LEARNED_NO_REPLACEMENT_SCAN_PRESSURE`)
    pub bcp_learned_no_replacement_scan_pressure: bool,
    /// `--sat-bcp-learned-1963-identity` (was `AY_SAT_BCP_LEARNED_1963_IDENTITY`)
    pub bcp_learned_1963_identity: bool,
    /// `--sat-bcp-learned-1963-pressure-reduction` (was `AY_SAT_BCP_LEARNED_1963_PRESSURE_REDUCTION`)
    pub bcp_learned_1963_pressure_reduction: bool,
    /// `--sat-bcp-learned-1963-pressure-retention` (was `AY_SAT_BCP_LEARNED_1963_PRESSURE_RETENTION`)
    pub bcp_learned_1963_pressure_retention: bool,
    /// `--sat-bcp-disable-learned-1963-no-replacement-unit-blocker-refresh` (was `AY_SAT_BCP_DISABLE_LEARNED_1963_NO_REPLACEMENT_UNIT_BLOCKER_REFRESH`)
    pub bcp_disable_learned_1963_no_replacement_unit_blocker_refresh: bool,
    /// `--sat-inprocessing-yield-productivity-rescue` (was `AY_SAT_INPROCESSING_YIELD_PRODUCTIVITY_RESCUE`)
    pub inprocessing_yield_productivity_rescue: bool,
    /// M2 FLIP (2026-08-19): default ON — paired full-400 300s proof-mode
    /// lost 0 / gained 2 with median 0.0s delta on the common set, and the
    /// 900s boundary confirmation was clean (ab_lrat_clamp_rescue_300s.json,
    /// ab_lrat_clamp_confirm_900s.json). `--sat-lrat-proof-clamp-probe-rescue
    /// false` is the opt-out; None = ON.
    pub lrat_proof_clamp_probe_rescue: Option<bool>,
    /// M3 FLIP (2026-08-19): default ON — paired full-400 300s proof-mode
    /// lost 0 / gained 1, and the 900s confirmation held the gain (arm 430s
    /// vs base timeout at 900s) with zero regressions
    /// (ab_backbone_cooldown_300s.json + _confirm_900s.json).
    /// `--sat-yield-rescue-backbone-cooldown false` is the opt-out; None = ON.
    pub yield_rescue_backbone_cooldown: Option<bool>,
    /// `--sat-bounded-backbone-zero-decompose-backoff` (was `AY_SAT_BOUNDED_BACKBONE_ZERO_DECOMPOSE_BACKOFF`)
    pub bounded_backbone_zero_decompose_backoff: bool,
    /// `--sat-bcp-learned-1963-blocker-cert-shadow` (was `AY_SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW`)
    pub bcp_learned_1963_blocker_cert_shadow: bool,
    /// `--sat-bcp-search-inplace-watch-scan <bool>` (tri-state, was `AY_SAT_BCP_SEARCH_INPLACE_WATCH_SCAN`; None = default ON)
    pub bcp_search_inplace_watch_scan: Option<bool>,
    /// `--sat-backbone-post-vivify-binary-admission <bool>` (tri-state, was `AY_SAT_BACKBONE_POST_VIVIFY_BINARY_ADMISSION`; None = default ON)
    pub backbone_post_vivify_binary_admission: Option<bool>,
    /// `--sat-finalize-rescue <bool>` (tri-state, was `AY_AB_FINALIZE_RESCUE`; None = default ON)
    pub finalize_rescue: Option<bool>,
    /// `--sat-bcp-learned-1963-tail-reorder-swap-budget <n>` (was `AY_SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAP_BUDGET`)
    pub bcp_learned_1963_tail_reorder_swap_budget: Option<u64>,
    /// `--sat-bcp-learned-1963-blocker-cert-elision` (the run.sh
    /// profile pair travels as CLI args now — was env-exported)
    pub bcp_learned_1963_blocker_cert_elision: bool,
    /// `--sat-bcp-learned-1963-blocker-cert-false-reject-demote`
    pub bcp_learned_1963_blocker_cert_false_reject_demote: bool,
    /// `--sat-dense-clique-php-proof-route`
    pub dense_clique_php_proof_route: bool,
    /// `--sat-xor-proof-route <bool>` (task #20). M7 FLIP (2026-08-21):
    /// default ON — paired full-400 300s proof-mode gained 6 / lost 1, and
    /// the 900s confirmation was STRICTLY dominant (lost 0 / gained 3: three
    /// XOR-structured instances the base cannot solve at triple budget fall
    /// in 0.7-2.3s; the 300s loss was boundary variance). Certificates
    /// externally checked throughout (ab_xor_proof_route_300s.json +
    /// _confirm_900s.json). `false` is the opt-out; None = ON.
    pub xor_proof_route: Option<bool>,
    /// `--sat-gf-probe <bool>` (bare-numeric landing). Default ON — the
    /// GF(p) one-hot linear-system startup probe constructs models for
    /// random mod-p linear-system CNFs (the SAT-COMP 2026 "1".."16"
    /// family) in milliseconds via structural detection + dense Gaussian
    /// elimination. Detection is strict and every model is fully
    /// self-verified before SAT is declared, so the off-family cost is one
    /// bailed classification scan. `false` is the opt-out; None = ON.
    pub gf_probe: Option<bool>,
    /// `--sat-indep-support <bool>` (independent-support branching landing).
    /// Default OFF — the brancher recovers gate definitions after
    /// preprocessing, computes an independent support (the variables that
    /// functionally determine all others) and restricts CDCL decisions to it
    /// while any support variable is unassigned. Decision-order only: an
    /// exhausted support falls through to unrestricted branching rather than
    /// signalling SAT, so it can never produce a wrong verdict. Shipped
    /// default-off because the paired A/B is not a clean win — see the
    /// landing commit. `true` opts in; None = OFF.
    pub indep_support: Option<bool>,
    /// `--sat-indep-enum <bool>` (bit-parallel support-enumeration landing).
    /// The startup probe that enumerates a tiny independent support
    /// bit-parallel (4096 candidate assignments per pass, packed one per bit
    /// of a machine word) and unit-propagates all of them simultaneously —
    /// the technique that cracks the SAT-COMP 2026 `xorshift` family. The
    /// admission gate is a support-size bound plus a projected-visit work
    /// bound, so off-family instances pay two integer comparisons; a
    /// surviving column is verified against every active clause before SAT is
    /// declared and exhaustion is never reported as UNSAT. Default ON —
    /// the paired A/B gained 5 / lost 0 and the gate fired on the target
    /// family and nothing else. `false` is the opt-out; None = ON.
    pub indep_enum: Option<bool>,
    /// `--sat-vivify-converge <bool>` (irredundant-vivification convergence
    /// landing). Default OFF. The shipped `vivify_preprocess` loop is capped
    /// at a formula-INDEPENDENT 4M ticks (4 rounds x `VIVIFY_MIN_EFFORT`), so
    /// on clause sets dominated by asymmetric tautologies it always stops on
    /// the round cap rather than at a fixed point. This arm replaces the
    /// constant with a budget linear in the irredundant literal count
    /// (`VIVIFY_CONVERGE_TICKS_PER_LITERAL`, ceilinged by
    /// `VIVIFY_CONVERGE_MAX_TICKS`/`_MAX_ROUNDS`/`_WALL_SECS`) and lets the
    /// loop run until a round strengthens nothing. Vivification only
    /// strengthens or deletes redundant clauses, so the arm cannot change a
    /// verdict — it trades preprocessing time for a smaller formula. Shipped
    /// default-off pending the full-corpus paired A/B. `true` opts in;
    /// None = OFF.
    pub vivify_converge: Option<bool>,
    /// `--sat-large-rephase-walk <bool>` (large-structured rephase/walk
    /// landing). Default OFF. Formulas above
    /// `VERY_LARGE_FORMULA_STABLE_BIAS_THRESHOLD` (1M original clauses)
    /// currently have rephasing switched off wholesale at solve entry, and the
    /// rephase walk additionally refuses any DB over 2M active clauses — so on
    /// multi-million-clause structured instances AY logs `walk_ms: 0` while
    /// kissat (whose only walk bound is `MAX_WALK_REF` = 2^31-1 clause
    /// references, i.e. effectively none) runs several walks. This arm keeps
    /// rephasing enabled in that band and lifts the rephase-walk gate to the
    /// same effective bound, so the tick-proportional walk budget decides the
    /// effort rather than a size cliff. Phase-only: walk writes saved phases
    /// and any full model it finds is verified before SAT is declared, so the
    /// arm cannot change a verdict's correctness.
    ///
    /// MEASURED NEGATIVE — kept as a sweepable arm, not a candidate flip.
    /// The gate turns out to exist for a good reason, exactly the one its own
    /// comment gives: AY's walk setup is not incremental, so each call costs
    /// O(clauses). On the witness at 300s the arm buys 4 walks for 44.8s of
    /// the 300s budget (14.9%) and the instance still returns UNKNOWN; on
    /// spg_200_301 (315,093 vars / 1,546,049 clauses) it buys 5 walks for
    /// 5.3s of 60s and LOSES the solve (UNSAT@30.2s -> UNKNOWN@60s). Lifting
    /// the cap is only worth revisiting once walk setup is incremental.
    /// `true` opts in; None = OFF.
    pub large_rephase_walk: Option<bool>,
    /// `--sat-mode-equiticks-large <bool>` (large-structured stabilization
    /// share landing). Default OFF. Enables the equal-effort stable tick
    /// budget — the same mechanism `mode_equiticks` selects, kissat
    /// `update_mode_limit` (`mode.c:69-110`) — but ONLY for formulas above
    /// `VERY_LARGE_FORMULA_STABLE_BIAS_THRESHOLD` (1M original clauses).
    ///
    /// The default schedule budgets each stable phase as
    /// `stabilize_tick_inc * nlogpow4(phase)`, where `stabilize_tick_inc` is
    /// frozen from the ticks of the first 1000 conflicts. On formulas where
    /// ticks-per-conflict grows by an order of magnitude as the learned DB
    /// fills, that frozen base starves stable mode: measured on
    /// cabp-V-nos6.mtx.rnd-k275 at 300s, 22.3% of search ticks in stable
    /// against kissat's 50/50 equal-effort design; the arm moves it to 48.2%.
    ///
    /// `mode_equiticks` (the global force) still wins when it is set to
    /// `Some(_)`, so this only fills in the `None` case. It is a separate
    /// field because the global arm carries its own measured full-400
    /// negative on the SMALL/MID band (<= 300K clauses, ratio <= 20) — a band
    /// that by construction excludes everything this one touches.
    ///
    /// NOT A FREE WIN, hence default-off: the share it buys is paid for by
    /// large UNSAT instances, which want focused mode's short proofs. Measured
    /// on spg_200_301 (315,093 vars / 1,546,049 clauses, UNSAT): stable tick
    /// share 7.6% -> 48.0%, solve time 26.4s -> 58.2s. The corpus A/B has to
    /// weigh that against the model-finding side. `true` opts in; None = OFF.
    pub mode_equiticks_large: Option<bool>,
    /// `--sat-bve-giant-raw <bool>` (giant raw-BVE route re-arm). Default OFF.
    /// Re-opens the compiled-but-inert giant raw-BVE unlock
    /// (`VariantConfig::bve_giant_raw_route_active`, see that predicate for the
    /// band) and, when armed, admits the re-pinned clause ceiling
    /// `BVE_GIANT_RAW_MAX_CLAUSES`.
    ///
    /// WHY IT EXISTS AGAIN. The route was retired in `d2bd18e6e2` as a
    /// "measured-negative opt-in", but the two measurements behind that label
    /// (`877271de86` 2026-07-11 and `d47bf815de`) both read
    /// "counters move, no verdict flip at 120s, controls held" — no regression
    /// was ever attributed to it. Both were taken on `9d7caee5`/`ac388757`
    /// only, and both PAIRED the route with the additive Pass-1 fastelim
    /// budget, which has since shipped DEFAULT ON above 200K vars
    /// (`bve::additive_fastelim_default`). So the composition that produced
    /// those numbers is now half-default, and the arm has never been measured
    /// on its own.
    ///
    /// WHY THE CEILING MOVES WITH IT. `BVE_GIANT_RAW_MAX_CLAUSES` is 8M for
    /// one stated reason — it is "equal to `AUTO_CONGRUENCE_MAX_CLAUSES` for
    /// the probe-reachable-band reason", i.e. the band is meant to be exactly
    /// "the AUTO collapse probe RAN and found no substitution structure". That
    /// probe band was later raised to `AUTO_CONGRUENCE_GIANT_MAX_VARS` /
    /// `AUTO_CONGRUENCE_GIANT_MAX_CLAUSES` (4M/10M, default ON off the proof
    /// path) and the giant-raw ceilings were never re-pinned to it. The
    /// consequence is arithmetic, not opinion: the whole `cabp-V-nos6` family
    /// (1.53M vars / 8.60M clauses, density 5.6) sits inside the raised probe
    /// band and outside the stale 8M ceiling, so arming the route alone leaves
    /// it refused. Only the CLAUSE arm is re-pinned; the 2M VAR ceiling is
    /// untouched, which is what keeps the giant SAT floor controls `4d6e18e5`
    /// (7.3M vars) and `00fd8ac9` (23.4M vars) excluded by construction.
    ///
    /// Scheduling/eligibility only — BVE reconstruction, model validation and
    /// DRAT emission are untouched, so the arm cannot change a verdict's
    /// correctness. Fails closed under LRAT (the route predicate refuses
    /// `VariantProofMode::Lrat` before reading this field), so any proof-mode
    /// A/B of it must be run on a DRAT surface. `true` opts in; None = OFF.
    pub bve_giant_raw: Option<bool>,
    /// `--sat-two-stage-clause-management <bool>` (LBD-free two-stage learned
    /// clause retention). Default OFF; `true` opts in, `false` is the explicit
    /// opt-out, `None` = OFF.
    ///
    /// Ports the clause-management policy of Cai, Zhang, Shi, Tao and Xu,
    /// "Rethinking Clause Management for CDCL SAT Solvers" (arXiv:2602.20829,
    /// 3rd place Main and Main UNSAT 2026, implemented in `kissat-eda` — "EDA"
    /// names the authors' lab, not the technique). The policy replaces LBD as
    /// the deletion key entirely:
    ///
    /// - `OnLearnedClause(c)`: `score(c) <- 1`.
    /// - `OnClauseUse(c)`: `score(c) += 1` when `c` forces a literal during BCP
    ///   OR serves as a reason during conflict analysis.
    /// - `OnPeriodicDecay()`: every `T = 4096` conflicts, `score <- max(0, score - 1)`
    ///   for every learned clause.
    /// - `TwoStageReduction()`: stage 1 keeps every clause with `score > 0`;
    ///   stage 2 takes the `score == 0` residue, sorts it by clause length
    ///   DESCENDING, and deletes the leading `percent`, where
    ///   `percent = 0.90 - (0.90 - 0.50) / log10(r + 9)` and `r` is the
    ///   reduction round.
    ///
    /// WHY IT IS A CANDIDATE FOR AY. Measured head to head on `vdw_4_7_n109`,
    /// same machine, both reaching UNSAT: AY needs 10,127,993 conflicts where
    /// kissat 4.0.4 needs 5,371,681, while props/conflict (16.6 vs 16.5) and
    /// decisions/conflict (1.18 vs 1.18) are identical. The search shape
    /// matches; only the number of conflicts needed to finish differs, which
    /// isolates the deficit to learned-clause retention quality.
    ///
    /// WHAT IT CHANGES IN AY. Only the reduce RANKING and the KEEP/DELETE
    /// decision. The reduction TRIGGER (`next_reduce_db`, the
    /// `L += 1000*sqrt(r+1)` schedule) is untouched, so an eventual corpus A/B
    /// is not confounded by a scheduling change. Scheduling-only: deletion goes
    /// through the same `delete_clause_unchecked` path with the same reason,
    /// IC3-lemma and LRAT-retention protections, so the arm cannot change a
    /// verdict's correctness — but it DOES change which clauses are deleted, so
    /// every proof it produces must still be checked externally.
    ///
    /// The ablation in the paper (60 solved for both stages, 56 for stage 1
    /// alone, 53 for stage 2 alone) says the two stages are only useful
    /// together, so this is a single switch rather than two.
    pub two_stage_clause_management: Option<bool>,
    /// `--sat-memory-aware-clause-db <bool>`. Size the learned clause
    /// database against the process `--memory` budget instead of against
    /// nothing at all. Default OFF pending its own paired A/B; `true` opts in,
    /// `None` = OFF.
    ///
    /// THE DEFECT IT FIXES. `Solver::max_clause_db_bytes` — the byte trigger
    /// in `should_reduce_db` / `explicit_reduce_pressure` — defaults to `None`,
    /// and the DIMACS entry points never set it; only the BV, strings and
    /// resolution-DAG paths do. So a `ay solve --competition --memory 6000`
    /// run on a CNF has NO connection between the budget it was given and the
    /// size of the database it builds. The budget is enforced only by
    /// observers: the advisory gate trips at 95% of it and the watchdog
    /// publishes `c memout` / `s UNKNOWN`. The run does not degrade, it aborts
    /// — a capability failure, where the solver never gets to try.
    ///
    /// With the ceiling armed (see
    /// `Solver::arm_clause_db_budget_from_process_limit`) the same pressure
    /// instead routes into machinery that already exists: `reduce_db` fires
    /// early, sweeps level-0-satisfied clauses, and compacts the arena.
    ///
    /// Scheduling only — it changes WHEN reduction fires and therefore which
    /// learned clauses survive, exactly like every other reduction-cadence
    /// knob. Deletion still goes through `delete_clause_unchecked` with the
    /// same reason, IC3-lemma and LRAT-retention protections, so it cannot
    /// change a verdict's correctness; it CAN change which proof is emitted, so
    /// UNSAT certificates produced under it must still be checked externally.
    pub memory_aware_clause_db: Option<bool>,
    /// `--sat-congruence-exact-gate-table <bool>`. Default OFF; `true`
    /// opts in, `None` = OFF.
    ///
    /// The congruence fixpoint's gate table used to remove a gate's entry by
    /// RECOMPUTING its signature under the current union-find. A gate is
    /// rewritten precisely because a merge changed one of its inputs'
    /// representatives, so the recomputed key differs from the one the gate was
    /// filed under, the removal misses, and the entry is stranded — one stranded
    /// entry per rewrite, unbounded.
    ///
    /// Measured at `b2258ab6` on SAT-COMP 2026 `post-cbmc-aes-ee-r2` (33 MB
    /// input, 28 of 31 official solvers solve it): 17.6 GB resident, `c memout`
    /// 8 s in against `--memory 6000`; 705 MB with `--disable congruence`.
    ///
    /// ON keys the removal off the signature the gate was actually filed under.
    /// That is semantics-preserving, not merely smaller: every key the table can
    /// be queried with comes out of `canonicalize`, which maps inputs through
    /// `uf.find`, so a matchable key holds only current representatives — while a
    /// stranded key is stranded exactly because a merge demoted one of its
    /// literals, and the union-find only merges further. Stranded keys are
    /// unmatchable, so dropping them loses no equivalence.
    ///
    /// Shipped OFF anyway: arming it ALONE does not convert the witness it was
    /// derived from — `post-cbmc-aes-ee-r2` still memouts at 4842 MB with it on
    /// — so the gate table is not where the bulk of that 17.6 GB lives. A change
    /// to a core preprocessing path with a cost and no measured benefit does not
    /// get a default; flip it on a paired corpus A/B.
    pub congruence_exact_gate_table: Option<bool>,
    /// `--sat-congruence-bounded-occs <bool>`. Default ON since 2026-09-15;
    /// `false` opts out.
    ///
    /// The congruence fixpoint re-pushes a gate onto its inputs' occurrence
    /// lists on every reinsertion, so a gate rewritten `n` times appears `n`
    /// times. ON collapses a list when it doubles, keeping it at O(gates using
    /// the literal) rather than O(rewrites touching it). Measured before the
    /// flip: it converts 5553fec2's memory-out into a verified UNSAT, and a full
    /// solve of 36 sampled instances is byte-identical with and without it.
    pub congruence_bounded_occs: Option<bool>,
    /// `--sat-eager-subsume-unlink-binaries <bool>`. Default OFF; `true` opts in.
    ///
    /// Eager subsumption marks a subsumed learned clause garbage and keeps its
    /// data for reason pointers. A long clause's watches are dirtied for the
    /// targeted flush, but a binary's are left in place. When the subsumer is the
    /// binary's duplicate, the husk stays watched until a flush removes its
    /// entries one list at a time. ON unlinks both watches at once, as on-the-fly
    /// subsumption does, so no half-removed binary reaches BCP or a graph pass. A
    /// binary subsumed by a unit is satisfied at level 0 and is left alone.
    /// Default OFF: it changes which watch entries propagate, so it changes the
    /// search trajectory; measure it before adopting.
    pub eager_subsume_unlink_binaries: Option<bool>,
    /// `--sat-conflict-cap <N>`. Unset by default. A counted stop for screens:
    /// the DIMACS search answers UNKNOWN at its N-th conflict, so two runs under
    /// `--sat-deterministic-inproc` stop at the same point under any load. It
    /// sets the solver's conflict budget, which only the budget check reads.
    pub conflict_cap: Option<u64>,
    /// `--sat-proof-min-free-bytes <BYTES>`. The free space the DIMACS proof
    /// writer keeps on the proof's own filesystem. Default 2 GiB since
    /// 2026-09-20; `0` turns the reserve off. When a probe finds less than this
    /// free, the writer stops the PROOF and not the search, exactly as a real
    /// ENOSPC does (77d0e04fb): a SAT answer still prints its verified model, an
    /// UNSAT answer prints the reason and `s UNKNOWN`. Measured: the three
    /// instances an 8 GB size cap stopped answer nothing when uncapped at 1500 s,
    /// and a proof large enough to be unverifiable scores what no proof scores,
    /// so the policy guards the disk rather than the size
    /// (competition/proof-posture-parity/HANDOFF-2026-09-10.md, drive#92).
    pub proof_min_free_bytes: Option<u64>,
    /// `--sat-proof-cap-bytes <BYTES>`. Unset by default: no size ceiling. When
    /// set, the DIMACS proof writer stops the proof at that many bytes, through
    /// the same latch as the reserve. It exists for a run that must bound its
    /// output explicitly; the default policy is the reserve above, because a
    /// ceiling can only lose an UNSAT that the disk could have held.
    pub proof_cap_bytes: Option<u64>,
    /// `--sat-symmetry-large-caps <bool>`. Default ON since 2026-09-17; `false` opts out. ON
    /// raises the orbitope and aux-free SR caps (2M, 1M) to 8M, and the orbitope detector's 1M
    /// to match; IR caps stay. Lever 2 of the SAT plan (proof-posture-parity); `size_caps.rs`.
    pub symmetry_large_caps: Option<bool>,
    /// `--sat-factor-large <bool>`. Default ON since 2026-09-18; `false` opts out. ON lets
    /// clause factoring run on formulas the expensive-pass size gate refuses (over 200K
    /// variables or 3M clauses, up to 2M variables, 10M clauses and density 20), opening
    /// its size and delay gates there. Lever 3 of competition/proof-posture-parity/PLAN-next-
    /// sat-levers.md; see `solver/factor_large.rs`.
    pub factor_large: Option<bool>,
    /// `--sat-subst-auto-giant-proof <bool>`. Default OFF; `true` arms the giant
    /// congruence band (4M variables, 10M clauses, the 12 s preprocessing budget)
    /// under the DRAT posture, which the shipped VeriPB surface resolves to. Today
    /// that band is non-proof only. Lever 4 of
    /// competition/proof-posture-parity/PLAN-next-sat-levers-2.md; see
    /// `subst_auto_giant_band_active` in `variant.rs`.
    pub subst_auto_giant_proof: Option<bool>,
    /// `--sat-bve-ext-cooccur <bool>`. Default OFF; `true` lets bounded variable
    /// elimination eliminate an original variable whose clauses also hold a live
    /// extension variable (one introduced by factoring or SBVA). Today such a
    /// variable is skipped (#8397 guard, `inprocessing/bve/body.rs`), which after a
    /// productive factor pass refuses most of the formula to BVE; the skips are
    /// counted in `sat.bve_ext_cooccur_skips`. Reconstruction handles any
    /// elimination order (each eliminated variable's clauses are pushed with their
    /// witness and replayed in reverse), so the guard is a belt on a fixed bug.
    pub bve_ext_cooccur: Option<bool>,
    /// `--sat-bve-bound-progress <bool>`. Default OFF; `true` lets a complete BVE
    /// phase that eliminated nothing raise the growth bound and re-queue every
    /// variable for the next phase (Kissat's `set_next_elimination_bound`);
    /// today only a productive phase moves the bound, so an unproductive one
    /// parks BVE at its bound until the fixpoint guard sees new units.
    pub bve_bound_progress: Option<bool>,
    /// `--sat-giant-band-max-vars <N>`. Default 2,000,000; raises the variable
    /// ceiling of the giant raw-BVE band (`BVE_GIANT_RAW_MAX_VARS`) and of the
    /// `--sat-factor-large` band (`FACTOR_LARGE_MAX_VARS`) together. Plan-2
    /// lever 7 (competition/proof-posture-parity/PLAN-next-sat-levers-2.md): the
    /// six official instances between 2M and 4.1M variables (baseballcover x2,
    /// newpol32-4, T90, T92, g2-T97) have no BVE route today; 4.1M admits them
    /// and keeps the giant SAT controls (7.3M and 23.4M variables) out.
    pub giant_band_max_vars: Option<usize>,
    /// `--sat-giant-inproc-permille <N>`. Default unset (the shipped budgets);
    /// on a formula above 1,000,000 variables it sets the vivification effort
    /// to `N` per mille of the search ticks (shipped 100) and the failed-literal
    /// probe effort to `N / 4` (shipped 25 on large formulas). On the
    /// baseballcover pair (3.56M variables) vivification and probing take two
    /// thirds of the wall at the shipped budgets, a vivify tick costing about
    /// 15 search ticks there (README, "Plan-2 lever 7, Stage 0").
    pub giant_inproc_permille: Option<u64>,
    /// `--sat-chrono <bool>`. Default unset (shipped: on); `false` turns
    /// chronological backtracking off, so every conflict backjumps to its
    /// asserting level (CaDiCaL `chrono=0`). For A/B; note that
    /// `sat.chrono_bt` counts the chronological branch and the trail-reuse
    /// partial backjumps together (a quarter of the conflicts on stable-400),
    /// while Kissat's `chronological` counter is the 100-level branch alone.
    pub chrono: Option<bool>,
    /// `--sat-chrono-reuse-trail <bool>`. Default unset (shipped: on);
    /// `false` keeps the plain backjump when the skip is within the limit
    /// instead of CaDiCaL's `chronoreusetrail` search for the best trail
    /// position (Kissat has no such rule).
    pub chrono_reuse_trail: Option<bool>,
    /// `--sat-factor-max-density <f>`. Default unset. The factor pass (at
    /// preprocessing and in search) is skipped on a formula whose density,
    /// irredundant clauses over structural variables, is above `f`. For A/B on
    /// the dense band (density above 12, at most 150K variables), where no
    /// BVE route eliminates the extension variables back (Kissat eliminates
    /// most of them: stable-400, 1,130 factored, 1,023 eliminated) and
    /// factoring off counted at 0.24 to 0.5 of the propagations on the
    /// stable-400, ER, SGI, schooltt, 5x-1xxxxx, qwh and vdw rows
    /// (2026-09-19, `miss-screen-nofactor.tsv`).
    pub factor_max_density: Option<f64>,
    /// `--sat-sbva-max-density <f>`. **Default 12 since 2026-09-22**; a value
    /// above any real density opts out. SBVA is skipped above this density,
    /// because its extension variables persist wherever BVE has no route to
    /// remove them — the dense band (vdwb_k6_n250: 3,649 on 250 originals;
    /// plan-2 section 8). Adopted on the two-sample rule: the cap answers
    /// QuasiGroup-4-12_c18 three times in three at 64.2-64.6 s where the tip
    /// answers once in three at 297.05 s, and at 1500 s in 124.63 s against
    /// 654.00 s — a 5.2x speed-up, not new reach; on the uniform 24 nothing
    /// changes but 2.8 s of PAR-2
    /// (competition/proof-posture-parity/l8-sbva-cap-verdict.tsv).
    pub sbva_max_density: Option<f64>,
    /// `--sat-elim-density-irredundant <bool>`. Default unset: the in-search
    /// elimination gates (the dense skip at 50, the factor-dense band at 90)
    /// read the database's density, learned clauses included, which opens the
    /// factor-dense band on formulas of density 50 to 90 once the learned
    /// database has grown; `true` reads the formula's density (irredundant
    /// clauses over structural variables) instead. Measured: the default
    /// answers rpoc_xits_09 (density 61) UNSAT in 27 s through that opening,
    /// `true` does not answer it at 300 s (2026-09-20); on stable-400 the
    /// opening costs 3.7x the propagations per conflict.
    pub elim_density_irredundant: Option<bool>,
    /// `--sat-inproc-nlogn-schedule <bool>`. Default unset: the inprocessing
    /// round interval is a 1K-2K conflict base times 3 to the power of the
    /// consecutive rounds that simplified under 1 percent of the active
    /// clauses (#8134, #8361), which on a hard UNSAT formula compounds until
    /// inprocessing stops (schooltt-5-3: 8 rounds in 8.6M conflicts, one per
    /// million; Kissat runs 34 probe rounds and 60 vivifications in the 2.1M
    /// conflicts it needs). `true` takes Kissat's schedule: the interval grows
    /// as k log10(k + 9) in the number of rounds, scaled once by the formula's
    /// size (`kissat_probe_interval`), with no productivity feedback; and the
    /// passes the rounds run are budgeted as Kissat budgets them: the rephase
    /// walk's effort reference is the search ticks since the last round
    /// (`compute_walk_effort_kissat`; 600 ms per walk against Kissat's 18 ms
    /// before) and an in-search sweep's candidate simulation is charged to the
    /// sweep's tick budget (64 passes over the formula per sweep before,
    /// about a second each on schooltt-5-3).
    pub inproc_nlogn_schedule: Option<bool>,
    /// `--sat-reduce-low-permille <n>`. Default unset (shipped: 750). The low
    /// end of the dynamic reduce fraction: a reduction deletes
    /// `high - (high - low) / log10(reductions + 9)` of its tier-3 candidates
    /// (high 900). 750 is CaDiCaL's fixed `reducetarget` (#8448) on top of
    /// Kissat's `1000 * sqrt(reductions)` interval; Kissat's own low end is
    /// `reducelow` 500, so it deletes 50 to 73 percent where AY deletes 75 to
    /// 85, and on schooltt-5-3 ends its run holding 80K redundant clauses to
    /// AY's 20K (Kissat 2.1M conflicts, AY 8.2M). `500` is Kissat's rule.
    pub reduce_low_permille: Option<u64>,
    /// `--sat-stacked-backbone <bool>`. Default unset (follows
    /// `--sat-inproc-nlogn-schedule`): Kissat's stacked binary backbone
    /// (`backbone_stacked.rs`) in place of the per-literal one. Its own
    /// switch so it can be counted and shipped without the schedule: on the
    /// 146-miss screen the old backbone cost 269 s to the stacked one's 33 s
    /// with more units (2026-09-21).
    pub stacked_backbone: Option<bool>,
    /// `--sat-vivify-generations <bool>`. Default unset (follows the schedule
    /// switch): vivification tries every clause once per generation
    /// (`VIVIFY_TRIED_BIT`) instead of re-trying the best-scored ones every
    /// call.
    pub vivify_generations: Option<bool>,
    /// `--sat-sweep-passes <bool>`. Default unset (follows the schedule
    /// switch): the in-search sweep charges all its work to its budget and
    /// keeps per-variable pass marks (and the bounded-CDCL backbone its own),
    /// so a budget-cut pass resumes instead of starting at variable 0.
    pub sweep_passes: Option<bool>,
    /// `--sat-tier-histogram-binaries <bool>`. Default unset (off): whether
    /// binary learned clauses used in conflict analysis feed the used-glue
    /// histogram the dynamic reduction tiers are computed from. Kissat never
    /// bumps binaries; with them counted, the tiers collapsed to 1 / 2 on
    /// schooltt-5-3 (Kissat 7 / 12). `true` restores the old accounting.
    pub tier_histogram_binaries: Option<bool>,
    /// `--sat-keep-learned-binaries <bool>`. Default unset (off): learned
    /// binary clauses are never reduction candidates, as in Kissat, where
    /// binary clauses live only in the watch lists and `collect_reducibles`
    /// never sees them. AY scans them on every reduction and protects the
    /// ones with a literal assigned above the root (`binary_clause_may_
    /// support_the_trail`): 167K such scans per reduction on SDP_134_18_4334.
    pub keep_learned_binaries: Option<bool>,
    /// `--sat-blanket-trail-protection <bool>`. Default unset (off): the
    /// reduction guards that keep every learned binary or hyper clause with
    /// a literal assigned above the root apply only under jump reasons,
    /// where binary reasons are literal-encoded and the reason marks cannot
    /// name the clause. `true` applies them everywhere, as before.
    pub blanket_trail_protection: Option<bool>,
    /// `--sat-branch-mab <bool>`. Default unset: the Default variant runs the
    /// MAB-UCB1 brancher (VSIDS against CHB in stable mode) only on the
    /// official LRAT route; every other posture, the shipped VeriPB one
    /// included, runs the legacy coupled brancher. `true` applies the
    /// official route's rule (MAB-UCB1 unless the small dense exception) on
    /// every posture; `false` forces the legacy brancher everywhere.
    pub branch_mab: Option<bool>,
    /// `--sat-bve-kissat-schedule <bool>`. Default unset: in-search BVE is
    /// rescheduled `BVE_INTERVAL_BASE x (phases + 1) x log2(density) x
    /// 2^unproductive` conflicts after each phase, the preprocessing phases
    /// included, so a dense formula whose preprocessing phases hit the
    /// candidate cap starts search with BVE due only after ~200K conflicts.
    /// `true` schedules it as Kissat schedules `eliminate`: `eliminateint`
    /// (500) x n log n of the phases x the formula-size scale, no
    /// unproductive backoff, the preprocessing phases counted as one, and a
    /// complete unproductive phase raises the elimination bound.
    pub bve_kissat_schedule: Option<bool>,
    /// `--sat-bve-post-factor-band <bool>`. Default OFF; `true` re-judges the
    /// sparse band that arms BVE on the Default route (density at most
    /// `--sat-bve-sparse-max-density`, 12, and at most
    /// `--sat-bve-sparse-max-vars` active variables) on the formula factoring
    /// leaves, not on the input. Factoring rewrites at-most-one-heavy formulas
    /// into sparse ones — qwh.60.1728 enters at 21.6 clauses per variable and
    /// leaves factoring near 4 — so the input gate keeps BVE off exactly where
    /// Kissat eliminates 69 percent of the variables after factoring and
    /// answers in 31 s, while ay runs 5,000 s without one BVE round.
    pub bve_post_factor_band: Option<bool>,
    /// `--sat-bve-dense-by-effort <bool>`. Default OFF; `true` together with
    /// `--sat-bve-kissat-schedule true` drops the inprocessing BVE density
    /// gate (no BVE above 50 clauses per variable, or above 20 with more than
    /// 3M clauses) and leaves elimination bounded by Kissat's effort rule, a
    /// tenth of the search ticks since the last elimination. Kissat has no
    /// density gate: on E00X23 (139 clauses per variable) it extracts 80K gates,
    /// eliminates 35 percent of the variables and answers UNSAT in 962 s, where
    /// ay never attempts elimination. Without the Kissat schedule the gate stays.
    pub bve_dense_by_effort: Option<bool>,
    /// `--sat-bump-binary-reasons <bool>`. Default OFF; `true` makes
    /// reason-side bumping follow binary literal reasons (#8034) the way it
    /// follows clause reasons, as Kissat's `analyze_reason_side_literals`
    /// does. Binary literal reasons exist only on formulas of at least 99
    /// percent binary clauses without LRAT; there the reason side of almost
    /// every learned literal was skipped.
    pub bump_binary_reasons: Option<bool>,
    /// `--sat-veripb-hints <bool>`. Default OFF; `true` writes learned clauses
    /// on the VeriPB route as annotated RUP (`rup <C> : <ids> ;`), their
    /// antecedents read off the trail (`solver/veripb_hints.rs`). SAT-COMP 2026
    /// elaborates every VeriPB proof for CakePB, and an unannotated `rup` makes
    /// the elaborator search the whole database: a 3.9 GB ER_500_50_1 proof
    /// was still checking after 7 CPU hours.
    pub veripb_hints: Option<bool>,
    /// `--sat-bve-gate-complete <bool>`. Default OFF; `true` lets BVE restrict
    /// resolution to gate × non-gate pairs for any variable whose gate is
    /// proved complete per candidate (`bve/gate_complete.rs`), as Kissat and
    /// CaDiCaL do for every gate. Off, only variables all of whose clauses are
    /// gate clauses qualify (the June 2026 clamp), so the XOR family's gate
    /// variables are refused: on sbdp4_138_2 Kissat eliminates 945 variables,
    /// 931 by gates, and AY refuses 472 of them at the growth bound.
    pub bve_gate_complete: Option<bool>,
    /// `--sat-stable-ema <bool>`. Default ON (unset); `false` drops the Glucose
    /// EMA restart that stable mode adds on top of reluctant doubling, so stable
    /// mode restarts on reluctant doubling alone, as Kissat and CaDiCaL do. On
    /// qwh.60.1728 (SAT) the EMA fired 113,852 times against 1,928 reluctant
    /// restarts (one per 40-58 conflicts; Kissat's stable mode restarts once per
    /// 1,740) and ay needed 9.3M conflicts where Kissat needs 159K.
    pub stable_ema: Option<bool>,
    /// `--sat-reduce-kissat-tiers <bool>`. Default OFF (CaDiCaL's rule); `true`
    /// computes tier2 past the tier1 glue and reduces against the stable-mode
    /// tier2, as Kissat 4.0.4 does, so a recently used clause up to that glue
    /// is kept (`solver/tier_state.rs`). On E00X23 AY's focused tier2 was 2 and
    /// it needed 3.1x Kissat's conflicts on the cube {1175, 1267}.
    pub reduce_kissat_tiers: Option<bool>,
    /// `--sat-very-large-band <bool>`. Default ON (unset); `false` skips the
    /// #8655 policy for formulas above 1M original clauses (stable start, VSIDS
    /// decay 0.97/0.99, scaled focused restart gate, no rephasing, no stable
    /// EMA) and gives them the 100K-1M treatment. The band was tuned on deep
    /// BMC unrollings; in SAT-COMP 2026 it holds 101 instances, of which ay
    /// (B2) answers 56 at the calibrated budget and the winner 76.
    pub very_large_band: Option<bool>,
    /// `--sat-reduce-large-cap <bool>`. Default ON (unset); `false` drops the
    /// 5,000-conflict ceiling on the reduce interval for formulas above 100K
    /// original clauses, leaving Kissat's `1000 * sqrt(reductions)` schedule.
    /// The cap was put in for learned-clause bloat on deep BMC (#8655); it
    /// applies to 221 of the 400 SAT-COMP 2026 instances.
    pub reduce_large_cap: Option<bool>,
    /// `--sat-live-size-gates <bool>`. Default OFF; `true` sizes a formula by
    /// its live variables (neither fixed, eliminated nor substituted) where the
    /// expensive-pass gates and the post-collapse BVE reopen read the parsed
    /// count. Compaction keeps fixed variables, so a formula that collapses at
    /// the root never shrinks: b54b26f3 (3.56M variables) fixes 3.01M of them
    /// as Kissat does, but then searches 550K definitional variables with no
    /// BVE, subsumption or sweep (30,800 propagations per conflict), where
    /// Kissat eliminates 538K and needs 859.
    pub live_size_gates: Option<bool>,
    /// `--sat-stable-lock-at <CONFLICTS>`. Unset: never. At that conflict count
    /// kissat-eda's classifier scores the (glue, size) histogram of the learned
    /// clauses so far and a non-negative score locks stable mode for the rest
    /// of the run (`solver/stable_lock.rs`; kissat-eda decides at 500,000). On
    /// booth_dadda the lock is most of kissat-eda's 2.3x over Kissat 4.0.2.
    pub stable_lock_at: Option<u64>,
    /// `--sat-stable-lock-ungated <bool>`: lock at `--sat-stable-lock-at`
    /// whatever the classifier says (the A/B arm for the lock alone).
    pub stable_lock_ungated: Option<bool>,
    /// `--sat-stable-lock-revert-two-stage <bool>`: with
    /// `--sat-two-stage-clause-management true`, turn the two-stage policy off
    /// when the classifier declines to lock, as kissat-eda-2 does with its
    /// usage-based retention (booth_dadda: lock alone 14.1M conflicts, lock with
    /// two-stage 8.95M; kissat-eda-2 solved 240 of 400 against Kissat's 238).
    pub stable_lock_revert_two_stage: Option<bool>,
    /// `--sat-stable-lock-two-stage <bool>`: switch the two-stage policy on at
    /// the lock, so only locked formulas change retention.
    pub stable_lock_two_stage: Option<bool>,
    /// `--sat-stable-lock-second-gate <bool>`: kissat-eda-3's rule. The first
    /// classifier alone switches the two-stage retention on (with
    /// `--sat-stable-lock-two-stage`); locking stable mode also needs its second
    /// model's score to be non-negative.
    pub stable_lock_second_gate: Option<bool>,
    /// `--sat-indep-enum-max-secs <SECS>`: ceiling on the independent-support
    /// enumeration's slice (default 800 s; `solver/indep_enum.rs`).
    pub indep_enum_max_secs: Option<u64>,
    /// `--sat-transred-propagation-effort <bool>`: budget transitive reduction
    /// in search propagations, as its documentation and CaDiCaL say, instead of
    /// search ticks (a several times larger unit).
    pub transred_propagation_effort: Option<bool>,
    /// `--sat-reorder-kissat <bool>`: Kissat's clause-weighted reorder at any
    /// size, from the search loop in both modes every 10K x n conflicts
    /// (`solver/inprocessing/reorder.rs`). On knight_18 Kissat's model follows
    /// a reorder in 6 of 7 solves and `--reorder=0` fails 4 of 4; AY turns
    /// reorder off above 50K variables.
    pub reorder_kissat: Option<bool>,
    /// `--sat-rephase-shuffle <bool>`. Default ON (unset); `false` keeps the
    /// decision order at a rephase instead of shuffling scores or the queue
    /// (CaDiCaL's `shuffle` defaults to off; Kissat has none).
    pub rephase_shuffle: Option<bool>,
    /// `--sat-bcp-move-on-true <bool>`: when the replacement literal found for
    /// a long-clause watch is already true, move the watch there as Kissat
    /// does (proplit.h:137-147) instead of keeping it with that literal as
    /// its blocker (CaDiCaL's policy, AY's default).
    pub bcp_move_on_true: Option<bool>,
    /// `--sat-target-kissat <bool>`: Kissat's target-phase rules. The target
    /// mark is not reset when stable mode starts, compaction sets the target
    /// and best marks to the number of active variables with such a phase, and
    /// saving copies the values of the assigned variables only. Emulating AY's
    /// rules inside Kissat on c8cde50f costs 21x (the reset) and 6.2x (the
    /// compaction rule); AY with the Kissat rules, pure stable and the Kissat
    /// reorder is SAT in 221 s where every other arm fails at 900 s.
    pub target_kissat: Option<bool>,
    /// `--sat-walk-kissat <bool>`: every local-search walk starts from the
    /// current phases and writes back only if it lowered the number of broken
    /// clauses, as Kissat's walk.c does. By default AY continues from the
    /// previous walk's result and always writes back, overwriting the saved
    /// phases after a walk that found nothing (c8cde50f diagnosis).
    pub walk_kissat: Option<bool>,
    /// `--sat-jump-reasons-kissat <bool>`: binary propagations store jump
    /// reasons (a binary-implied literal's reason is its implier's reason, so
    /// reasons point at chain roots) on the formulas where Kissat 4.0.4
    /// actually does it. Kissat's gate compares a 0-100 percentage against
    /// `bigbigfraction / 1000.0` (`classify.c:14-17`), so it holds on any
    /// formula over 100K clauses with at least 0.99 percent binary clauses,
    /// not the 99 percent AY copied; Kissat also takes the jump when it
    /// assigns a learned binary clause's UIP (`assign.c:38`). Reclassified at
    /// level 0 after in-search simplification and, off to on only, at each
    /// reduction (`solver/jump_reasons.rs`).
    pub jump_reasons_kissat: Option<bool>,
    /// `--sat-rephase-kissat <bool>`: Kissat 4.0.4's rephasing
    /// (`rephase.c`). Rephase in stable mode only, on the schedule best, walk,
    /// inverted, best, walk, original from the first rephase, without
    /// shuffling the decision order, with the walk allowed at any formula size
    /// (Kissat's `MAX_WALK_REF`), and first due at 1,000 conflicts whatever the
    /// formula's size. AY's default rephases in both modes on CaDiCaL's
    /// schedule, shuffles the scores or queue at every rephase, caps the walk
    /// at 2M active clauses, delays the first rephase by log10(clauses) above
    /// 100K clauses and turns rephasing off above 1M.
    pub rephase_kissat: Option<bool>,
    /// `--sat-bump-reasons-kissat <bool>`: Kissat 4.0.4's reason-side bumping
    /// (`analyze.c:139-212`): one level deep in both modes, skipped once the
    /// decision rate reaches 10 per conflict, the rate a bias-corrected EMA
    /// (window 1e5, `smooth.c`) kept per mode, and one delay for both modes.
    /// AY's default is CaDiCaL's: two levels in stable mode, a rate limit of
    /// 100, and an uncorrected EMA that starts at zero, so it reads near zero
    /// for the first tens of thousands of conflicts and always bumps there.
    pub bump_reasons_kissat: Option<bool>,
    /// `--sat-mode-length-kissat <bool>`: the first mode phase lasts
    /// Kissat's `modeinit` = 1,000 conflicts whatever the formula size
    /// (`mode.c:19-35`). AY's default multiplies it by log10(clauses) above
    /// 100K clauses (about 6.9x on an 8.6M-clause formula), and every later
    /// focused phase scales from it, so AY alternates modes that much less
    /// often than Kissat. The very-large band sets its own schedule and is
    /// unaffected.
    pub mode_length_kissat: Option<bool>,
    /// `--sat-large-inproc <bool>`: in-search equivalence reasoning
    /// (substitution/decompose, congruence, subsumption, backbone,
    /// transitive reduction, sweeping) on formulas over 200K variables or 3M
    /// clauses, up to 32M active clauses, where Kissat runs every such pass
    /// at any size under its effort limits. AY's default skips them all above
    /// the 200K-variable / 3M-clause gates, so a 4M-variable circuit
    /// (cc42cc7a) is searched with probing and vivification only. The dense
    /// guards are unchanged, and factoring, dedup, SBVA, BCE, CCE and
    /// conditioning keep the default gates.
    pub large_inproc: Option<bool>,
    /// `--sat-probe-phases-kissat <bool>`: probing, in-tree probing and
    /// transitive reduction backtrack without saving phases or updating the
    /// target and best phases, as Kissat does while `probing` is set
    /// (`inlineassign.h:52-58`, `backtrack.c:39-40`). AY's default saves the
    /// polarity of every probe assignment and can record a probe trail as the
    /// new target or best phases; backbone and vivification already skip it.
    pub probe_phases_kissat: Option<bool>,
    /// `--sat-indep-enum-and <bool>`: the bit-parallel support enumeration
    /// compiles two-input AND gates (`(o ∨ ¬a ∨ ¬b)` with `(¬o ∨ a)`,
    /// `(¬o ∨ b)`) into one constraint kind, one visit where the clause
    /// encoding takes three (`solver/indep_enum.rs`, `engine/visit.rs`).
    pub indep_enum_and: Option<bool>,
    /// `--sat-reduce-kissat-recompute <bool>`: recompute the current mode's
    /// tier limits at the START of every reduction, as Kissat does
    /// (`reduce.c:159`, `tiers.c`). AY's default is CaDiCaL's schedule: at
    /// the end of a reduction, backing off to every 65,536 conflicts, so late
    /// in a run the limits a reduction uses can be tens of reductions stale
    /// (on cabp AY's stable tier2 sat at 6 where Kissat's is about 127).
    pub reduce_kissat_recompute: Option<bool>,
    /// `--sat-target-kissat-pop <bool>` (with `--sat-target-kissat`): after a
    /// conflict, the saved target and best phases leave out the conflict
    /// level's assignments. Kissat pops the conflict level before it saves
    /// (`backtrack.c:156-161`); `--sat-target-kissat` alone saves the values
    /// of every assigned variable, the failing level's included.
    pub target_kissat_pop: Option<bool>,
    /// `--sat-restart-gate-kissat <bool>`: Kissat 4.0.4's focused-mode restart
    /// spacing (`restart.c:14-51`, `restartint` 1): a restart needs
    /// trunc(log10(restarts + 9)) conflicts since the last one (1 before the
    /// first), counting restarts of both modes, fires on `fast >= 1.1 slow`,
    /// never at level 0, and the count starts afresh on entering focused mode
    /// (`mode.c`). AY's default is CaDiCaL's: two more conflicts at every
    /// point (3 to 6; at least 11 on small dense formulas), a strict EMA test,
    /// and a count carried over from the stable phase.
    pub restart_gate_kissat: Option<bool>,
    /// `--sat-initial-phase-kissat <bool>`: search starts with no seeded
    /// phases, so every first decision is true, as in Kissat 4.0.4
    /// (`decide.c:155-200`; `walkinitially` is never read). AY's default runs
    /// warmup (which seeds the target), a ProbSAT startup walk and
    /// Jeroslow-Wang polarities before the first decision. The rephase walk
    /// and warmup are untouched.
    pub initial_phase_kissat: Option<bool>,
    /// `--sat-reduce-schedule-kissat <bool>`: the parts of Kissat 4.0.4's
    /// reduce schedule no other switch covers. The first reduction comes at
    /// `reduceinit` = 1,000 conflicts (AY: 300); no small-formula interval
    /// cap; no learned-count trigger (Kissat reduces on its conflict limit
    /// only, `reduce.c:14-22`); and `--sat-reduce-low-permille` also governs
    /// small dense formulas (AY otherwise uses 850 there). Pair it with
    /// `--sat-reduce-large-cap false --sat-reduce-low-permille 500
    /// --sat-reduce-kissat-recompute true` for Kissat's whole schedule.
    pub reduce_schedule_kissat: Option<bool>,
    /// `--sat-best-stable-kissat <bool>`: the best phases are updated in
    /// stable mode only, as Kissat updates target and best there only
    /// (`backtrack.c:38-44`); AY's default also records focused-mode trails.
    pub best_stable_kissat: Option<bool>,
    /// `--sat-restart-fixpoint-kissat <bool>`: restarts and mode switches are
    /// decided only at a propagation fixpoint with no conflict and above level
    /// 0 (Kissat `search.c:195-209`), not also right after conflict analysis
    /// before the learned clause's UIP is propagated.
    pub restart_fixpoint_kissat: Option<bool>,
    /// `--sat-mode-delta-kissat <bool>`: the focused-phase length is
    /// `trunc(len * n * log10(n + 9)^4)` in floating point, as Kissat's
    /// `kissat_nlogpown` (`mode.c`); AY's default truncates n*log^4 first.
    pub mode_delta_kissat: Option<bool>,
    /// `--sat-inproc-passes-kissat <bool>`: the search runs none of the
    /// in-search passes Kissat 4.0.4 does not have: failed-literal probing
    /// with hyper-binary resolution, in-tree probing, HTR, SBVA and
    /// lookahead (Kissat's probe round is congruence, backbone, vivify,
    /// sweep, substitute and factor, `probe.c`). Implies
    /// `--sat-probe-phases-kissat`.
    pub inproc_passes_kissat: Option<bool>,
    /// `--sat-backbone-binary-kissat <bool>`: no bounded-CDCL backbone, in
    /// search or preprocessing; Kissat's backbone is the binary-implication
    /// one only (`backbone.c`), and AY's bounded one adds its probe
    /// conflicts, learned clauses and bumps to the search.
    pub backbone_binary_kissat: Option<bool>,
    /// `--sat-randec-kissat <bool>`: Kissat 4.0.4's random decision
    /// sequences (`decide.c:57-124`): in focused mode, every decision is
    /// random for trunc(10 log10(n + 9)) conflicts, a sequence starting when
    /// the search is at level 0 past a conflict limit that is 500 at first
    /// and then conflicts + trunc(500 log10(n + 9)), and on every entry into
    /// focused mode unless one is running. AY's default checks its limit
    /// before the running sequence, and starting a sequence pushes the limit
    /// ahead, so each sequence after the first makes one random decision.
    pub randec_kissat: Option<bool>,
    /// `--sat-preprocess-kissat <bool>`: preprocessing runs Kissat 4.0.4's
    /// `probe_initially` (`probe.c:45-66`) and nothing else: congruence, then
    /// substitution if it found anything; the binary-implication backbone;
    /// sweeping at any size, then substitution if it rewrote anything;
    /// substitution if none ran yet; factoring behind the
    /// log10(active) <= eliminations + 4 gate. No elimination, probing,
    /// ternary resolution, subsumption or vivification before search
    /// (`fastel` is off in 4.0.4), so elimination first runs in search.
    pub preprocess_kissat: Option<bool>,
    /// `--sat-subst-kissat <bool>`: Kissat 4.0.4's substitution schedule.
    /// The AUTO collapse probe and the dense disarm no longer turn congruence
    /// and decompose off for the solve; in search, congruence runs in every
    /// simplification round its Kissat delay counter allows (one more skipped
    /// round after each closure merging under 0.1% of the active variables,
    /// half as many after a productive one) and decompose runs after it
    /// every time (`probe.c:26-43`, `congruence.c:4594-4632`). Off under
    /// LRAT.
    pub subst_kissat: Option<bool>,
    /// `--sat-queue-freeze-kissat <bool>`: the focused-mode VMTF queue does
    /// not move in stable mode (Kissat bump.c:103-112 moves variables to the
    /// front only when focused), so each focused phase resumes the queue the
    /// previous one left, searching from its end (queue.c:13-20). AY's
    /// default records stable bumps in `bump_order` and rebuilds the queue
    /// from them on every switch into focused mode.
    pub queue_freeze_kissat: Option<bool>,
    /// `--sat-analysis-ticks-kissat <bool>`: conflict analysis charges
    /// search ticks as Kissat 4.0.4 does, one per large (3+ literal) reason
    /// visited by minimization, shrinking and reason-side bumping
    /// (minimize.c:51, shrink.c:179, analyze.c:158) and nothing for the
    /// conflict, the resolution loop or binary reasons. AY's default also
    /// charges those, which moves `--sat-mode-equiticks` switches and every
    /// tick-proportional inprocessing budget.
    pub analysis_ticks_kissat: Option<bool>,
    /// `--sat-two-stage-warm-scores-kissat <bool>`: the two-stage retention
    /// scores (birth 1, +1 per propagation and per use as a reason, -1 every
    /// 4096 conflicts) are kept from conflict 1, as kissat-eda keeps its
    /// clause stamps. AY's default starts them when the stable lock turns the
    /// policy on at 500K conflicts, so its first reduction sees every older
    /// learned clause at score 0 and ranks them by length alone.
    pub two_stage_warm_scores_kissat: Option<bool>,
    /// `--sat-vivify-kissat <bool>`: Kissat 4.0.4's vivification schedule
    /// (vivify.c:1395-1458). Vivification runs in every simplification round
    /// under one budget, 10% of the search ticks since the last round (10M
    /// floor), split cumulatively 3:3:1:3 over focused tiers 1-3 and the
    /// irredundant clauses. The irredundant share waits out a Kissat delay
    /// counter. The default's separate intervals, tick threshold, stable
    /// tier2 boundary and small-dense skip are bypassed.
    pub vivify_kissat: Option<bool>,
    /// `--sat-eliminate-cadence-kissat <bool>`: Kissat 4.0.4's in-search
    /// elimination cadence (eliminate.c:420-600). The interval is NLOG2N,
    /// `500 x n log10(n + 9)^2` scaled by the clause count, over the in-search
    /// elimination calls only. Each phase runs one round. The bound moves
    /// 0, 1, 2, 4, 8, 16 after every call. AY's `--sat-bve-kissat-schedule`
    /// uses NLOGN over every BVE call (preprocessing included), runs up to
    /// three rounds with fresh budgets, and moves the bound only when the
    /// candidates ran out.
    pub eliminate_cadence_kissat: Option<bool>,
    /// `--sat-binary-irredundant-kissat <bool>`: learned binary clauses are
    /// irredundant, as every binary is in Kissat 4.0.4 (clause.c:64-117). At
    /// each reduction and simplification round every live learned binary,
    /// hyper resolvents excepted, is promoted. Elimination, factoring and
    /// the clause-count scales then see it, and reduction never deletes it.
    /// Off under LRAT and in incremental or scoped solving.
    pub binary_irredundant_kissat: Option<bool>,
    /// `--sat-probe-round-kissat <bool>` (only with
    /// `--sat-inproc-nlogn-schedule`): the simplification round follows
    /// Kissat 4.0.4's probe cadence (probe.c, kimits.c). Preprocessing counts
    /// as the first probing, and the first round comes 100 scaled conflicts
    /// in. Sweep, transitive reduction, factoring and the backbone run in
    /// every round rather than on their own conflict intervals and tick
    /// thresholds; sweeping waits out a Kissat delay counter, and factoring
    /// keeps its delay gate.
    pub probe_round_kissat: Option<bool>,
    /// `--sat-reduce-protect-kissat <bool>`: glue-tier reduction protects as
    /// Kissat 4.0.4 does (reduce.c:65-87). Glue-1 clauses are kept only
    /// while used, not permanently, and a reason's `used` is decremented
    /// before it is skipped. Pair with `--sat-keep-learned-binaries`.
    pub reduce_protect_kissat: Option<bool>,
    /// `--sat-subsume-kissat <bool>`: forward subsumption as in Kissat 4.0.4
    /// (eliminate.c:438-449, forward.c:140-142). It runs only before and
    /// between elimination rounds, never in the simplification round's front
    /// half or after vivification, and it considers irredundant clauses and
    /// binaries only. Learned clauses are left to eager subsumption and
    /// vivification.
    pub subsume_kissat: Option<bool>,
    /// `--sat-learned-order-kissat <bool>`: a learned clause's literals from
    /// position 1 on are sorted by descending level, analysis order kept
    /// within a level, as Kissat 4.0.4 orders them (analyze.c:560-561). The
    /// replacement-watch scan then meets recently decided literals first.
    pub learned_order_kissat: Option<bool>,
    /// `--sat-factor-schedule-kissat <bool>`: factoring's delay gate is
    /// Kissat 4.0.4's (factor.c:1068-1085). It opens when floor(log10(active
    /// variables)) <= in-search eliminations + 4, at every size. AY's
    /// counts every BVE call, preprocessing included, and the factor-large
    /// band bypasses it.
    pub factor_schedule_kissat: Option<bool>,
    /// `--sat-reluctant-cap-kissat <bool>`: stable-mode reluctant doubling
    /// resets once v x 1024 would exceed 2^20 conflicts, as Kissat 4.0.4 caps
    /// the interval (reluctant.c:44-49, `reluctantlim`). AY capped v at 2^20,
    /// so intervals grew to 2^30; with the stable lock and no stable EMA,
    /// long runs stopped restarting after about 23M conflicts.
    pub reluctant_cap_kissat: Option<bool>,
    /// `--sat-reorder-weights-kissat <bool>`: reorder weights and timing as
    /// in Kissat 4.0.4 (reorder.c:14-112). Every binary between active
    /// variables weighs 1, learned ones included. Clause sizes are capped at
    /// 100, not 20. Weight ties keep queue order. The reorder waits for a
    /// natural level 0 rather than backtracking to it.
    pub reorder_weights_kissat: Option<bool>,
    /// `--sat-shrink-bump-uip-kissat <bool>`: when shrinking replaces a
    /// block by its block UIP, the UIP's variable is marked analyzed and so
    /// bumped with the learned clause, as in Kissat 4.0.4 (shrink.c:128-132).
    /// AY's default leaves it unbumped.
    pub shrink_bump_uip_kissat: Option<bool>,
    /// `--sat-shrink-removable-kissat <bool>`: when shrinking replaces a
    /// block by its block UIP, every literal the walk resolved becomes
    /// removable and the level's earliest seen trail position drops to the
    /// UIP's, as Kissat 4.0.4 marks its whole shrinkable set removable
    /// (shrink.c:22-45, 134) and has no trail abort (minimize.c:4-40). Higher
    /// blocks and fallback minimization then accept lower-level literals the
    /// UIP implies, as Kissat does (shrink.c:63-73). AY's default marks only
    /// the block literals and refuses any unmarked literal at or before the
    /// level's first clause literal.
    pub shrink_removable_kissat: Option<bool>,
    /// `--sat-sweep-env-kissat <bool>`: SAT sweeping in Kissat 4.0.4's
    /// environment (sweep.c). It starts at 256 variables, 1024 clauses and
    /// depth 2, and every completed pass doubles the counts and adds a layer,
    /// up to 8192, 32768 and 3. Variables are swept fewest occurrences first,
    /// each environment may spend the call's whole remaining tick budget, and
    /// every kitten model refines the candidates. In search it also charges
    /// all sweep work to the budget and drops the 200 ms wall cap. AY's
    /// default environment is fixed at 48 variables, 4096 clauses and depth
    /// 4, with 20,000 ticks per environment.
    pub sweep_env_kissat: Option<bool>,
    /// `--sat-compact-fixed <bool>`: variable compaction counts root-fixed
    /// variables as inactive and removes them, as CaDiCaL (compact.cpp) and
    /// Kissat (compact.c) do. A fixed variable is dropped once no clause
    /// mentions it, after a complete level-0 collection, and models read
    /// its saved root value. AY's default compacts away eliminated and
    /// substituted variables only.
    pub compact_fixed: Option<bool>,
    /// `--sat-vivify-asym-kissat <bool>`: vivification deletes an irredundant
    /// candidate whose probe ends in a conflict that needs every one of its
    /// literals when no learned clause is in the conflict's cone: the clause
    /// is an asymmetric tautology of the other irredundant clauses (Kissat
    /// 4.0.4 vivify.c:1181-1186). AY's default keeps it unchanged and deletes
    /// asymmetric tautologies only on the implied-literal path. A round's
    /// yield (the vivify delay and the irredundant backoff) then counts
    /// deletions as well as strengthenings, as Kissat counts every vivified
    /// clause (vivify.c:1454-1457).
    pub vivify_asym_kissat: Option<bool>,
    /// `--sat-vivify-order-kissat <bool>`: vivification assumes a candidate's
    /// literals in Kissat 4.0.4's order (vivify.c:24-56, 1015): by their
    /// occurrence count in the large (size > 2) live clauses, learned ones
    /// included, most frequent first, ties to the larger literal. AY's default
    /// orders by Jeroslow-Wang weights over all clauses, which short learned
    /// clauses dominate.
    pub vivify_order_kissat: Option<bool>,
}

static GLOBAL_SAT_AB_SWITCHES: OnceLock<SatAbSwitches> = OnceLock::new();

/// Install the SAT A/B opt-outs (first caller wins).
///
/// # Errors
///
/// The rejected value when a set was already installed.
#[expect(clippy::result_large_err, reason = "duplicate-set ownership")]
pub fn set_global_sat_ab_switches(switches: SatAbSwitches) -> Result<(), SatAbSwitches> {
    GLOBAL_SAT_AB_SWITCHES.set(switches)
}

/// The installed SAT A/B opt-outs, or the all-shipped default.
#[must_use]
pub fn sat_ab_switches() -> SatAbSwitches {
    if let Some(overridden) = consumer_test_override::CONSUMER_OVERRIDE.with(std::cell::Cell::get) {
        return overridden;
    }
    GLOBAL_SAT_AB_SWITCHES.get().copied().unwrap_or_default()
}

/// Consumer-crate test seam (same shape as
/// `ay_pb_core::ab_switches::consumer_test_override`): always compiled so a
/// consumer crate's own tests can scope switch values. Production code must
/// never touch it.
#[doc(hidden)]
pub mod consumer_test_override {
    use super::SatAbSwitches;

    thread_local! {
        pub(super) static CONSUMER_OVERRIDE: std::cell::Cell<Option<SatAbSwitches>> =
            const { std::cell::Cell::new(None) };
    }

    /// RAII guard restoring the previous override on drop.
    pub struct Guard(Option<SatAbSwitches>);

    impl Drop for Guard {
        fn drop(&mut self) {
            let prev = self.0;
            CONSUMER_OVERRIDE.with(|c| c.set(prev));
        }
    }

    /// Install a thread-scoped override for the current test.
    #[must_use]
    pub fn set(switches: SatAbSwitches) -> Guard {
        let prev = CONSUMER_OVERRIDE.with(|c| c.replace(Some(switches)));
        Guard(prev)
    }
}
