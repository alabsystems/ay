// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Process-constant SAT A/B switches installed by the CLI.

use std::sync::OnceLock;

/// SAT-engine A/B opt-outs, CLI-owned (B26: these replace never-set
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
    /// `--sat-no-factor-dense-init` (B33)
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
    /// `--sat-no-probe-route` (B34; was the AY_AB_PROBE_ROUTE=0 shim)
    pub no_probe_route: bool,
    /// `--sat-no-aggressive-route` (B34)
    pub no_aggressive_route: bool,
    /// `--sat-no-bve-sparse` (B34)
    pub no_bve_sparse: bool,
    /// `--sat-no-bve-post-collapse` (B34)
    pub no_bve_post_collapse: bool,
    /// `--sat-no-subst-auto` (B34; restores the pre-flip opt-in profile)
    pub no_subst_auto: bool,
    /// `--sat-subst-auto-uncapped` (B34; the historical `=1` UNCAPPED
    /// measurement semantics — disarms the dense-band guard rails)
    pub subst_auto_uncapped: bool,
    /// `--sat-no-drat-subst` (B34; force-clamp Decompose+Congruence on DRAT
    /// — the pre-2026-07-09 behavior. The old `=1` force-allow arm was
    /// registry-redundant and is gone.)
    pub no_drat_subst: bool,
    /// `--sat-bve-additive-fastelim` (B36; force the banded additive
    /// fast-elim ON past its band auto decision)
    pub bve_additive_fastelim: bool,
    /// `--sat-no-bve-additive-fastelim` (B36; force it OFF)
    pub no_bve_additive_fastelim: bool,
    /// `--sat-mode-equiticks <true|false>` (B43; was the
    /// `AY_AB_MODE_EQUITICKS` 1/0 tri-state — `Some(true)` forces the
    /// equal-effort stable budgeting ON everywhere, `Some(false)` forces it
    /// OFF, `None` = the shipped default-off resolution)
    pub mode_equiticks: Option<bool>,
    /// `--sat-eqt-progress <N>` (B43; `1` = the default progress-gate
    /// window, `N > 1` sets the window directly; `None`/other = gate inert)
    pub eqt_progress: Option<u64>,
    /// `--sat-congruence-memory-bound` (B43; re-arm the retired congruence
    /// fixpoint memory guard without re-deriving it)
    pub congruence_memory_bound: bool,
    /// `--sat-circuit-equiv-throughput-profile` (B43; opt in to the
    /// multiplier-equivalence throughput profile lane)
    pub circuit_equiv_throughput_profile: bool,
    /// `--sat-signed-symmetry` (B61; opt in to the signed lex-leader route —
    /// measured LOSING on the full 400 at 300s, kept as a sweepable arm)
    pub signed_symmetry: bool,
    /// `--sat-composite-symmetry` (B61; plain lex leaders remain no-proof-only;
    /// `--sat-symmetry-hhw` supplies the supported proof route)
    pub composite_symmetry: bool,
    /// `--sat-symmetry-hhw` (B61)
    pub symmetry_hhw: bool,
    /// `--sat-bve-sparse-max-vars <n>` (B65; raises/lowers the sparse-BVE
    /// variable ceiling — was `AY_BVE_SPARSE_MAX_VARS`)
    pub bve_sparse_max_vars: Option<usize>,
    /// `--sat-bve-sparse-max-density <f>` (B65)
    pub bve_sparse_max_density: Option<f64>,
    /// `--sat-deterministic-inproc <bool>` (B70; tri-state force of the
    /// default-ON deterministic inprocessing budget)
    pub deterministic_inproc: Option<bool>,
    /// `--sat-congruence-parity-trust` (B70; default-off trust arm)
    pub congruence_parity_trust: bool,
    // B75: the dimacs env-lever block becomes typed switches. Opt-in bools
    // default false = the shipped engine; tri-states default None = the
    // compiled default named at the read site.
    /// `--sat-bcp-telemetry` (B75; was `AY_BCP_TELEMETRY`)
    pub bcp_telemetry: bool,
    /// `--sat-bcp-lean` (B75; was `AY_SAT_BCP_LEAN`)
    pub bcp_lean: bool,
    /// `--sat-bcp-disable-trail-lookahead-prefetch` (B75; was `AY_SAT_BCP_DISABLE_TRAIL_LOOKAHEAD_PREFETCH`)
    pub bcp_disable_trail_lookahead_prefetch: bool,
    /// `--sat-bcp-advance-saved-pos` (B75; was `AY_SAT_BCP_ADVANCE_SAVED_POS`)
    pub bcp_advance_saved_pos: bool,
    /// `--sat-bcp-learned-1963-false-saved-pos-reset` (B75; was `AY_SAT_BCP_LEARNED_1963_FALSE_SAVED_POS_RESET`)
    pub bcp_learned_1963_false_saved_pos_reset: bool,
    /// `--sat-bcp-learned-1963-true-tail-relocation` (B75; was `AY_SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION`)
    pub bcp_learned_1963_true_tail_relocation: bool,
    /// `--sat-bcp-learned-618-true-tail-relocation` (B75; was `AY_SAT_BCP_LEARNED_618_TRUE_TAIL_RELOCATION`)
    pub bcp_learned_618_true_tail_relocation: bool,
    /// `--sat-bcp-learned-617-tail-reorder` (B75; was `AY_SAT_BCP_LEARNED_617_TAIL_REORDER`)
    pub bcp_learned_617_tail_reorder: bool,
    /// `--sat-bcp-learned-18-tail-reorder` (B75; was `AY_SAT_BCP_LEARNED_18_TAIL_REORDER`)
    pub bcp_learned_18_tail_reorder: bool,
    /// `--sat-bcp-learned-1963-tail-reorder` (B75; was `AY_SAT_BCP_LEARNED_1963_TAIL_REORDER`)
    pub bcp_learned_1963_tail_reorder: bool,
    /// `--sat-bve-occ-delta-validation` (B75; was `AY_SAT_BVE_OCC_DELTA_VALIDATION`)
    pub bve_occ_delta_validation: bool,
    /// `--sat-bve-occ-saved-state-reuse` (B75; was `AY_SAT_BVE_OCC_SAVED_STATE_REUSE`)
    pub bve_occ_saved_state_reuse: bool,
    /// `--sat-dense-mutex-focused-restart-gate` (B75; was `AY_SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE`)
    pub dense_mutex_focused_restart_gate: bool,
    /// `--sat-dense-clique-mab-branch` (B75; was `AY_SAT_DENSE_CLIQUE_MAB_BRANCH`)
    pub dense_clique_mab_branch: bool,
    /// `--sat-bve-lrat-scout-route` (B75; was `AY_SAT_BVE_LRAT_SCOUT_ROUTE`)
    pub bve_lrat_scout_route: bool,
    /// `--sat-fmla-decompose-lrat-preflight-route` (B75; was `AY_SAT_FMLA_DECOMPOSE_LRAT_PREFLIGHT_ROUTE`)
    pub fmla_decompose_lrat_preflight_route: bool,
    /// `--sat-dense-clique-scout` (B75; was `AY_SAT_DENSE_CLIQUE_SCOUT`)
    pub dense_clique_scout: bool,
    /// `--sat-multiplier-equiv-conservation-scout` (B75; was `AY_SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT`)
    pub multiplier_equiv_conservation_scout: bool,
    /// `--sat-bcp-learned-1963-used5-fsw-saved-pos-reset` (B75; was `AY_SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET`)
    pub bcp_learned_1963_used5_fsw_saved_pos_reset: bool,
    /// `--sat-bcp-learned-1963-fsw-conflict-saved-pos-reset` (B75; was `AY_SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET`)
    pub bcp_learned_1963_fsw_conflict_saved_pos_reset: bool,
    /// `--sat-bcp-learned-no-replacement-saved-pos-update` (B75; was `AY_SAT_BCP_LEARNED_NO_REPLACEMENT_SAVED_POS_UPDATE`)
    pub bcp_learned_no_replacement_saved_pos_update: bool,
    /// `--sat-bcp-learned-1963-fsw-gent-skip` (B75; was `AY_SAT_BCP_LEARNED_1963_FSW_GENT_SKIP`)
    pub bcp_learned_1963_fsw_gent_skip: bool,
    /// `--sat-bcp-learned-no-replacement-scan-pressure` (B75; was `AY_SAT_BCP_LEARNED_NO_REPLACEMENT_SCAN_PRESSURE`)
    pub bcp_learned_no_replacement_scan_pressure: bool,
    /// `--sat-bcp-learned-1963-identity` (B75; was `AY_SAT_BCP_LEARNED_1963_IDENTITY`)
    pub bcp_learned_1963_identity: bool,
    /// `--sat-bcp-learned-1963-pressure-reduction` (B75; was `AY_SAT_BCP_LEARNED_1963_PRESSURE_REDUCTION`)
    pub bcp_learned_1963_pressure_reduction: bool,
    /// `--sat-bcp-learned-1963-pressure-retention` (B75; was `AY_SAT_BCP_LEARNED_1963_PRESSURE_RETENTION`)
    pub bcp_learned_1963_pressure_retention: bool,
    /// `--sat-bcp-disable-learned-1963-no-replacement-unit-blocker-refresh` (B75; was `AY_SAT_BCP_DISABLE_LEARNED_1963_NO_REPLACEMENT_UNIT_BLOCKER_REFRESH`)
    pub bcp_disable_learned_1963_no_replacement_unit_blocker_refresh: bool,
    /// `--sat-inprocessing-yield-productivity-rescue` (B75; was `AY_SAT_INPROCESSING_YIELD_PRODUCTIVITY_RESCUE`)
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
    /// `--sat-bounded-backbone-zero-decompose-backoff` (B75; was `AY_SAT_BOUNDED_BACKBONE_ZERO_DECOMPOSE_BACKOFF`)
    pub bounded_backbone_zero_decompose_backoff: bool,
    /// `--sat-bcp-learned-1963-blocker-cert-shadow` (B75; was `AY_SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW`)
    pub bcp_learned_1963_blocker_cert_shadow: bool,
    /// `--sat-bcp-search-inplace-watch-scan <bool>` (B75; tri-state, was `AY_SAT_BCP_SEARCH_INPLACE_WATCH_SCAN`; None = default ON)
    pub bcp_search_inplace_watch_scan: Option<bool>,
    /// `--sat-backbone-post-vivify-binary-admission <bool>` (B75; tri-state, was `AY_SAT_BACKBONE_POST_VIVIFY_BINARY_ADMISSION`; None = default ON)
    pub backbone_post_vivify_binary_admission: Option<bool>,
    /// `--sat-finalize-rescue <bool>` (B75; tri-state, was `AY_AB_FINALIZE_RESCUE`; None = default ON)
    pub finalize_rescue: Option<bool>,
    /// `--sat-bcp-learned-1963-tail-reorder-swap-budget <n>` (B75; was `AY_SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAP_BUDGET`)
    pub bcp_learned_1963_tail_reorder_swap_budget: Option<u64>,
    /// `--sat-bcp-learned-1963-blocker-cert-elision` (B76; the run.sh
    /// profile pair travels as CLI args now — was env-exported)
    pub bcp_learned_1963_blocker_cert_elision: bool,
    /// `--sat-bcp-learned-1963-blocker-cert-false-reject-demote` (B76)
    pub bcp_learned_1963_blocker_cert_false_reject_demote: bool,
    /// `--sat-dense-clique-php-proof-route` (B76)
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
    /// WHY IT EXISTS AGAIN. The route was retired by B21 (`d2bd18e6e2`) as a
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
    /// `--sat-memory-aware-clause-db <bool>` (B77). Size the learned clause
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
    /// `--sat-congruence-exact-gate-table <bool>` (B77). Default OFF; `true`
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
    /// `--sat-congruence-bounded-occs <bool>` (B77). Default OFF; `true` opts in.
    ///
    /// The congruence fixpoint re-pushes a gate onto its inputs' occurrence
    /// lists on every reinsertion, so a gate rewritten `n` times appears `n`
    /// times. ON collapses a list when it doubles, keeping it at O(gates using
    /// the literal) rather than O(rewrites touching it).
    ///
    /// Default OFF because duplicates change how many times
    /// `rewrite_gate_after_merge` runs inside one drain — a scheduling change,
    /// not a pure lifetime fix — and it is unmeasured on the corpus.
    pub congruence_bounded_occs: Option<bool>,
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

/// Consumer-crate test seam (B61; same shape as
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
