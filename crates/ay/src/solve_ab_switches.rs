// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Typed solver A/B switches and their process-constant installation.

use super::SolveArgs;

/// Hidden sound-alternative switches used for A/B measurement.
#[derive(clap::Args, Default)]
pub(super) struct SolveAbSwitches {
    /// Quarantine the NIA clausal local-search lane (B16).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_nia_clausal_sls: bool,
    /// Disable cross-solve warm simplex state (B16).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_lra_warm_simplex: bool,
    /// Disable the EUF incremental disequality-undo lane (B30).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_euf_inc_diseq_undo: bool,
    /// Restore eager EUF propagation reasons (B30).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_euf_lazy_explain: bool,
    /// Disable lazy EUF no-propagation reasons (B30).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_euf_lazy_noprop: bool,
    /// Skip the LIA probe minimization scan (B30).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_lia_probe_scan: bool,

    /// Force the legacy LRA decision-suggestion scan (B30).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_lra_fast_decision: bool,

    /// Disable the S1 word-equation regex lane (B30).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_we_s1: bool,

    /// Disable the EUF incremental congruence-undo lane (B36).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_euf_inc_cong_undo: bool,

    /// Restore the Z3/Dantzig most-violated leaving-variable rule (B36).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_lra_shortest_poly: bool,

    /// Force the relevancy brancher off (0) or on (1; 2 adds the engage
    /// marker). Unset lets each lane decide (B36).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_relevancy: Option<u8>,

    /// Explicit FC global pair budget; unset arms the many-array autoscale
    /// (B36).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    fc_global_budget: Option<usize>,

    /// MILP-race gate diagnostics (B41).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    maxsat_debug: bool,

    /// Proof self-check mode: 1 warn, 2 strict (B41).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    proof_self_check: Option<u8>,

    /// Opt-in CHECKED CHC replay budget, seconds (B41).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_checked_replay: Option<u64>,

    /// Lift the XOR-extension clause cap (B41).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    xor_allow_large: bool,
    /// Allow residual-dominated XOR routing (B41).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    xor_allow_residual: bool,

    /// B42 dpll diagnostics (each replaces a keep-override env var).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    phase_trace: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    debug_cert: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    debug_qmg: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    model_reject_dump: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    debug_strict_oracle: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    g3_gate_dump: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    quiet_soundness_gate: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    rup_fallback_trace: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    lra_inc_engine_stats: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    lra_inc_engine_reverify: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    debug_no_terms: Option<String>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    proof_introspect: Option<String>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    proof_introspect_probe: Option<String>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    str_w4_work: Option<u64>,
    /// Finite-model MBQI lane per-invocation wall cap, ms (B43 A/B).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    fmq_lane_budget_ms: Option<u64>,
    /// Finite-model MBQI lane per-sub-solve ceiling, ms (B43 A/B).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    fmq_probe_ms: Option<u64>,
    /// Finite-model MBQI lane session decline seed, ms (B43 A/B).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    fmq_seed_ms: Option<u64>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_ab_subst_stats: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_ab_subst_dump_merges: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_ab_subst_dump_gates: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_ab_subst_dump_edges: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_ab_dump_db: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_factor_probe: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_probe_trace_dup: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_l0_unsat_trace: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_symmetry_trace: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_mem_probe: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_ab_triage_clause: Option<String>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_ab_triage_var: Option<u64>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_ab_triage_probe: Option<String>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_accept_profile: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_cata_trace: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_houdini_debug: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_imc_stats: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_proof_itp_stats: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_ice_dt_trace: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_dt_bmc_trace: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_v2_debug: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_ground_bt_debug: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_bmc_nested_debug: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_debug_marker_dag_verify: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_array_frontier_telemetry: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_cata_dump_abstract: Option<String>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_cata_dump_obligations: Option<String>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_dump_scalarized: Option<String>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_dump_failed_replay_obligation: Option<String>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_checksat_dump: Option<String>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_pdr_dump: Option<String>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_proof_itp_dump: Option<String>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_checksat_trace: Option<u8>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_cata: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_cata_v2: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_condense: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    euf_gap_stats: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    lia_instrument: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    probe_stats_every: Option<u64>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    str_nf_closures: Option<String>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    trace_cegqi_attr: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    debug_read_pin: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    f1_diag: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    census_trace: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    debug_pigeonhole: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    cert_debug: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    count_debug: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    tseitin_trace: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    debug_subst: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    debug_split_exit: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    debug_class_merge: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    milp_fastpath_debug: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    demand_debug: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    prop_debug: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    quant_stats: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    debug_fixup: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    debug_cegar: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    str_prepass_stats: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    milp_lane_trace: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    verify_mixed_strings_stats: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    a5_uf_eq_defer: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    spike_dump: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    spike_verbose: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    qfax_combiner_route: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    qfax_cegar: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    qfax_lanes_debug: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    probe_strict_check: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    probe_cert_reject: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    uflia_witness_debug: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    pb_sym_debug: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    pb_farkas_cert: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    qfax_neg_eq_witness: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    qfax_neg_chain_gate: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    vsids_decay: Option<f64>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    inprobe_mult: Option<f64>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    factor_elim_bound: Option<i64>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    pb_sls_endgame_threshold: Option<usize>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    dump_query_dir: Option<String>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    keep_alethe_artifacts: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_quant_unit_authority: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_skolem_witness_sat: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_singleton_carrier_mint: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_consequence_replay: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_quantified_shedding_yield: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_negated_exists_ground_inst: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_ground_conflict_decomp: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_fp_incremental: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    vacuous_marker_narrow: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    proj_axiom_budget: Option<usize>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    uflia_witness_complete: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    uflia_witness_parts: Option<String>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    uflia_fused_detour: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    verify_memo: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    pb_eqagg_debug: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    pb_bnb: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_pb_sls_feasfirst: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    pb_strict_optimum: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    pb_sls_unified: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    pb_proof_tap_soft_cap_mib: Option<u64>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sls_planted: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sls_sweep: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    oll_file: Option<String>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    oll_expect: Option<String>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    pb_debug_panic_on_incumbent: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_prune_conflict_experiments: Option<bool>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    debug_lazy_sync: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    debug_fc_sync: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    lra_warm_stats: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    fuzz_verbose: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    certora_trace: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    debug_abv_finite_array: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    debug_abv_packed_lookup: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    debug_ladder: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    debug_wgr: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    debug_completion_merge: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    debug_arith_oracle: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    debug_unwitnessed: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    cut_trace: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    dump_render: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_array_tree_refutation: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_dont_care_filter: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_intern: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_array_inv: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_dt_recursive_prefix: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    interface_diet: Option<String>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    bv_preprocess: Option<String>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    fc_cegar_iters: Option<u32>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    int_pigeonhole_enrich_k: Option<usize>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    ext_row_seed: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    debug_row_seed: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    dpll_mint_theory_vars: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    dpll_ite_lift: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    euf_bool_arg_repair: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    lra_warm_theory: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    force_array_euf: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    ab_maxsat_core_clause: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    ab_maxsat_descent_organic_slice: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    ab_maxsat_kick_gap_abs: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    ab_maxsat_descent_kick_scale: bool,
    /// `--uflia-arith-decisions` (B72): forward UFLIA arith decision hints.
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    uflia_arith_decisions: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    lra_float_layer: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    str_nf: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    debug_euf_init: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    euf_cong_undo_debug: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    euf_diseq_undo_debug: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    probe_prescreen: bool,
    #[arg(
        long,
        hide_short_help = true,
        hide_long_help = true,
        value_name = "MODE"
    )]
    lia_probe_qx: Option<String>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    probe_stats: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    debug_fixed_eqs: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    algebraic_stats: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    debug_arr_extract: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    weq5_shadow_dump: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    ic3_lane_debug: bool,
    #[arg(
        long,
        hide_short_help = true,
        hide_long_help = true,
        value_name = "PATH"
    )]
    ic3_lane_dump: Option<String>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    ic3_lane_noslice: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    reve_debug: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true, value_name = "N")]
    max_propagate_rounds: Option<u64>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    lra_cond_trail: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    euf_inc_neg_pop: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    nra_diag: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    nra_grid_probe: bool,
    #[arg(
        long,
        hide_short_help = true,
        hide_long_help = true,
        value_name = "ASSIGNMENTS"
    )]
    nra_witness: Option<String>,
    #[arg(
        long,
        hide_short_help = true,
        hide_long_help = true,
        value_name = "BOOL"
    )]
    quant_relevance: Option<bool>,
    #[arg(long, hide_short_help = true, hide_long_help = true, value_name = "N")]
    quant_relevance_k: Option<usize>,
    #[arg(long, hide_short_help = true, hide_long_help = true, value_name = "N")]
    quant_relevance_min: Option<usize>,
    #[arg(
        long,
        hide_short_help = true,
        hide_long_help = true,
        value_name = "BOOL"
    )]
    quant_relevance_model: Option<bool>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    quant_relevance_debug: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_deterministic_inproc: Option<bool>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_congruence_parity_trust: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bcp_telemetry: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bcp_lean: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bcp_disable_trail_lookahead_prefetch: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bcp_advance_saved_pos: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bcp_learned_1963_false_saved_pos_reset: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bcp_learned_1963_true_tail_relocation: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bcp_learned_618_true_tail_relocation: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bcp_learned_617_tail_reorder: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bcp_learned_18_tail_reorder: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bcp_learned_1963_tail_reorder: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bve_occ_delta_validation: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bve_occ_saved_state_reuse: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_dense_mutex_focused_restart_gate: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_dense_clique_mab_branch: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bve_lrat_scout_route: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_fmla_decompose_lrat_preflight_route: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_dense_clique_scout: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_multiplier_equiv_conservation_scout: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bcp_learned_1963_used5_fsw_saved_pos_reset: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bcp_learned_1963_fsw_conflict_saved_pos_reset: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bcp_learned_no_replacement_saved_pos_update: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bcp_learned_1963_fsw_gent_skip: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bcp_learned_no_replacement_scan_pressure: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bcp_learned_1963_identity: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bcp_learned_1963_pressure_reduction: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bcp_learned_1963_pressure_retention: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bcp_disable_learned_1963_no_replacement_unit_blocker_refresh: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_inprocessing_yield_productivity_rescue: bool,
    #[arg(
        long,
        hide_short_help = true,
        hide_long_help = true,
        value_name = "BOOL"
    )]
    sat_lrat_proof_clamp_probe_rescue: Option<bool>,
    #[arg(
        long,
        hide_short_help = true,
        hide_long_help = true,
        value_name = "BOOL"
    )]
    sat_yield_rescue_backbone_cooldown: Option<bool>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bounded_backbone_zero_decompose_backoff: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bcp_learned_1963_blocker_cert_shadow: bool,
    #[arg(
        long,
        hide_short_help = true,
        hide_long_help = true,
        value_name = "BOOL"
    )]
    sat_bcp_search_inplace_watch_scan: Option<bool>,
    #[arg(
        long,
        hide_short_help = true,
        hide_long_help = true,
        value_name = "BOOL"
    )]
    sat_backbone_post_vivify_binary_admission: Option<bool>,
    #[arg(
        long,
        hide_short_help = true,
        hide_long_help = true,
        value_name = "BOOL"
    )]
    sat_finalize_rescue: Option<bool>,
    #[arg(long, hide_short_help = true, hide_long_help = true, value_name = "N")]
    sat_bcp_learned_1963_tail_reorder_swap_budget: Option<u64>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bcp_learned_1963_blocker_cert_elision: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bcp_learned_1963_blocker_cert_false_reject_demote: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_dense_clique_php_proof_route: bool,
    #[arg(
        long,
        hide_short_help = true,
        hide_long_help = true,
        value_name = "BOOL"
    )]
    sat_xor_proof_route: Option<bool>,
    #[arg(
        long,
        hide_short_help = true,
        hide_long_help = true,
        value_name = "BOOL"
    )]
    sat_gf_probe: Option<bool>,
    #[arg(
        long,
        hide_short_help = true,
        hide_long_help = true,
        value_name = "BOOL"
    )]
    sat_indep_support: Option<bool>,
    #[arg(
        long,
        hide_short_help = true,
        hide_long_help = true,
        value_name = "BOOL"
    )]
    sat_indep_enum: Option<bool>,
    #[arg(
        long,
        hide_short_help = true,
        hide_long_help = true,
        value_name = "BOOL"
    )]
    sat_vivify_converge: Option<bool>,
    #[arg(
        long,
        hide_short_help = true,
        hide_long_help = true,
        value_name = "BOOL"
    )]
    sat_large_rephase_walk: Option<bool>,
    #[arg(
        long,
        hide_short_help = true,
        hide_long_help = true,
        value_name = "BOOL"
    )]
    sat_mode_equiticks_large: Option<bool>,
    /// Force the banded additive BVE fast-elim on (overrides the band auto decision; B36).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bve_additive_fastelim: bool,
    /// Force the banded additive BVE fast-elim off (B36).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_no_bve_additive_fastelim: bool,
    /// Disable CHC derivation expansion (B15).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_deriv_expansion: bool,
    /// Disable the CHC early safety check (B15).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_early_safety_check: bool,
    /// Disable CHC ground-witness solving (B15).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_ground_witness: bool,
    /// Disable CHC disequality-swap refinement (B15).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_diseq_swap: bool,
    /// Disable the CHC forward-simulation fix (B15).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_fwdsim_fix: bool,
    /// Disable guarded CHC implication hints (B15).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_guarded_impl_hints: bool,
    /// Disable the CHC Houdini phase-B fast path (B15).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_houdini_phaseb_fast: bool,
    /// Disable datatype-BMC definition elimination (B15).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_dt_bmc_elim: bool,
    /// CHC B27 opt-outs (each replaces a never-set default-on env var).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_bitblast_dynamic_abort: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_bmc_multipred_ts: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_bmc_ts_incremental: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_array_store_forwarding: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_cata_elements: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_ground_backtranslation: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_ground_table_concretization: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_houdini_bv: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_pc_split: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_split_sym: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_word_bv: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_may_pob: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_exec_dv_retry: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_exec_unknown_memo: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_front_probe_clamp: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_graph_collapse: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_houdini_disjunctive: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_houdini_stage5: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_imc_proof_itp: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_pdr_lemma_sanitize: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_tpa_fixpoint: bool,
    /// chc B33 opt-outs (each replaces a per-test env-steered kill switch).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_array_relational: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_array_relational_v2: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_dt_bmc: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_qual_mine: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    chc_no_qual_mixed: bool,
    /// dpll B28 opt-outs (each replaces a never-set default-on env var).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    dpll_no_abvfp_flatten: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    dpll_no_closed_sentence_cert: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    dpll_no_closed_sentence_unsat_cert: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    dpll_no_dt_uflia: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    dpll_no_dt_d1: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    dpll_no_euf_lnh: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    dpll_no_idl_engine: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    dpll_no_int_coloring: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    dpll_no_int_pigeonhole: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    dpll_no_lnh_leastidx: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    dpll_no_lra_inc_engine: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    dpll_no_lra_inc_engine_full: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    dpll_no_lra_inc_warm: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    dpll_no_nested_array_residue_rescue: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    dpll_no_prop_feedback: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    dpll_no_uc_lia_probe_fallthrough: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    dpll_no_uc_minimize_general: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    dpll_force_qfax_arr_bcp_lanes: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    dpll_no_rdl_engine: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    dpll_no_str_p2: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    dpll_no_str_p3: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    dpll_no_str_w4: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    dpll_no_str_w5: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    dpll_no_str_w6: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    dpll_no_str_w7: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    dpll_no_str_witness: bool,

    /// Disable the enum finite-domain SAT lane (B17).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_enum_sat: bool,
    /// Restore padded-superset unsat cores (B17).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_uc_minimize: bool,
    /// Restore the unconditional phase re-seed (B17).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    disable_phase_epoch_skip: bool,
    /// Disable the constant-interpretation certificate gate (B17).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_const_interp_cert: bool,
    /// Drop MaxSAT totalizer output equalities (B17).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    maxsat_no_tot_eqs: bool,
    /// Keep the preprocessed MaxSAT engine after a mostly-risky BCE
    /// reduction (B17).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    maxsat_no_bce_revert: bool,
    /// B32 maxsat/frontend opt-outs (each replaces a never-set env var).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    maxsat_no_am1_maxcover: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    maxsat_bce: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    maxsat_no_bmo: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    maxsat_no_cold_descent: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    maxsat_no_descent_residual: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    maxsat_no_dpw: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    maxsat_no_early_descent: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    maxsat_no_preproc: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    maxsat_no_milp_race: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_inc_linear_parse: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    no_milp_fastpath: bool,

    /// SAT engine A/B opt-outs (B26: each replaces a never-set default-on
    /// kill-switch env var; every default is the shipped engine).
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_no_bve_inst_gate: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_no_factor_dense_init: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_no_probe_route: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_no_aggressive_route: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_no_bve_sparse: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_no_bve_post_collapse: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_no_subst_auto: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_subst_auto_uncapped: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_no_drat_subst: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_no_bve_sparse_deep: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_no_dense_skip_lift: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_no_factor_bin_fastpath: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_no_factor_dense: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_no_lucky: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_no_midband_deep_restart: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_no_orbitope: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_no_orbitope_alo_columns: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_no_symmetry_sr_auxfree: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_mode_equiticks: Option<bool>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_eqt_progress: Option<u64>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_congruence_memory_bound: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_circuit_equiv_throughput_profile: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_signed_symmetry: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_composite_symmetry: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_symmetry_hhw: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bve_sparse_max_vars: Option<usize>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bve_sparse_max_density: Option<f64>,
    #[arg(
        long,
        hide_short_help = true,
        hide_long_help = true,
        value_name = "BOOL"
    )]
    sat_bve_giant_raw: Option<bool>,
    #[arg(
        long,
        hide_short_help = true,
        hide_long_help = true,
        value_name = "BOOL"
    )]
    sat_two_stage_clause_management: Option<bool>,
    #[arg(
        long,
        hide_short_help = true,
        hide_long_help = true,
        value_name = "BOOL"
    )]
    sat_memory_aware_clause_db: Option<bool>,
    #[arg(
        long,
        hide_short_help = true,
        hide_long_help = true,
        value_name = "BOOL"
    )]
    sat_congruence_exact_gate_table: Option<bool>,
    #[arg(
        long,
        hide_short_help = true,
        hide_long_help = true,
        value_name = "BOOL"
    )]
    sat_congruence_bounded_occs: Option<bool>,
}

include!("solve_ab_switches/test_support.rs");
include!("solve_ab_switches/solve_args_impl.rs");
