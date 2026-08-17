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
    no_consequence_replay: bool,
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
    sat_deterministic_inproc: Option<bool>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_congruence_parity_trust: bool,

    /// Force the banded additive BVE fast-elim on (overrides the band auto
    /// decision; B36).
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
    sat_signed_symmetry_sr: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_composite_symmetry: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_symmetry_sr: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_symmetry_hhw: bool,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bve_sparse_max_vars: Option<usize>,
    #[arg(long, hide_short_help = true, hide_long_help = true)]
    sat_bve_sparse_max_density: Option<f64>,
}

#[cfg(test)]
impl SolveAbSwitches {
    pub(super) fn b33_opt_outs(&self) -> [bool; 6] {
        [
            self.chc_no_array_relational,
            self.chc_no_array_relational_v2,
            self.chc_no_dt_bmc,
            self.chc_no_qual_mine,
            self.chc_no_qual_mixed,
            self.sat_no_factor_dense_init,
        ]
    }
}

impl SolveArgs {
    /// Install every process-constant solver switch in dependency order.
    pub(super) fn install_solver_switches(&self) {
        self.install_theory_disable_flags();
        self.install_sat_ab_switches();
    }

    /// Install miscellaneous CLI-owned settings, including the B17 MaxSAT pair.
    pub(super) fn install_misc_cli_flags(&self) {
        let sat_variant_from_cli = self.sat_variant.is_some();
        let sat_variant = self.sat_variant.clone().or_else(|| {
            std::env::var("AY_SAT_VARIANT")
                .ok()
                .map(|value| value.trim().to_string())
                .filter(|value| !value.is_empty())
        });
        let flags = ay_core::MiscCliFlags {
            dump_auflia_assertions: self.dump_auflia_assertions,
            sat_variant,
            sat_variant_from_cli,
            disabled_sat_startup_capabilities: super::disabled_sat_startup_capabilities(self),
            dpll_diagnostic_file: self
                .dpll_diagnostic_file
                .as_ref()
                .map(|path| path.to_string_lossy().into_owned()),
            dpll_diagnostic_enabled: self.dpll_diagnostic,
            dpll_trace_file: self
                .dpll_trace_file
                .as_ref()
                .map(|path| path.to_string_lossy().into_owned()),
            maxsat_no_tot_eqs: self.ab_switches.maxsat_no_tot_eqs,
            maxsat_no_bce_revert: self.ab_switches.maxsat_no_bce_revert,
            maxsat_no_am1_maxcover: self.ab_switches.maxsat_no_am1_maxcover,
            maxsat_bce: self.ab_switches.maxsat_bce,
            maxsat_no_bmo: self.ab_switches.maxsat_no_bmo,
            maxsat_no_cold_descent: self.ab_switches.maxsat_no_cold_descent,
            maxsat_no_descent_residual: self.ab_switches.maxsat_no_descent_residual,
            maxsat_no_dpw: self.ab_switches.maxsat_no_dpw,
            maxsat_no_early_descent: self.ab_switches.maxsat_no_early_descent,
            maxsat_no_preproc: self.ab_switches.maxsat_no_preproc,
            maxsat_no_milp_race: self.ab_switches.maxsat_no_milp_race,
            no_inc_linear_parse: self.ab_switches.no_inc_linear_parse,
            no_milp_fastpath: self.ab_switches.no_milp_fastpath,
            sat_relevancy: self.ab_switches.sat_relevancy,
            fc_global_budget: self.ab_switches.fc_global_budget,
            maxsat_debug: self.ab_switches.maxsat_debug,
            proof_self_check: self.ab_switches.proof_self_check,
            chc_checked_replay_secs: self.ab_switches.chc_checked_replay,
            xor_allow_large: self.ab_switches.xor_allow_large,
            xor_allow_residual: self.ab_switches.xor_allow_residual,
            phase_trace: self.ab_switches.phase_trace,
            debug_cert: self.ab_switches.debug_cert,
            debug_qmg: self.ab_switches.debug_qmg,
            model_reject_dump: self.ab_switches.model_reject_dump,
            debug_strict_oracle: self.ab_switches.debug_strict_oracle,
            g3_gate_dump: self.ab_switches.g3_gate_dump,
            quiet_soundness_gate: self.ab_switches.quiet_soundness_gate,
            rup_fallback_trace: self.ab_switches.rup_fallback_trace,
            lra_inc_engine_stats: self.ab_switches.lra_inc_engine_stats,
            lra_inc_engine_reverify: self.ab_switches.lra_inc_engine_reverify,
            debug_no_terms: self.ab_switches.debug_no_terms.clone(),
            proof_introspect: self.ab_switches.proof_introspect.clone(),
            proof_introspect_probe: self.ab_switches.proof_introspect_probe.clone(),
            str_w4_work: self.ab_switches.str_w4_work,
            ab_subst_stats: self.ab_switches.sat_ab_subst_stats,
            ab_subst_dump_merges: self.ab_switches.sat_ab_subst_dump_merges,
            ab_subst_dump_gates: self.ab_switches.sat_ab_subst_dump_gates,
            ab_subst_dump_edges: self.ab_switches.sat_ab_subst_dump_edges,
            ab_dump_db: self.ab_switches.sat_ab_dump_db,
            factor_probe: self.ab_switches.sat_factor_probe,
            probe_trace_dup: self.ab_switches.sat_probe_trace_dup,
            sat_l0_unsat_trace: self.ab_switches.sat_l0_unsat_trace,
            sat_symmetry_trace: self.ab_switches.sat_symmetry_trace,
            sat_mem_probe: self.ab_switches.sat_mem_probe,
            ab_triage_clause: self.ab_switches.sat_ab_triage_clause.clone(),
            ab_triage_var: self.ab_switches.sat_ab_triage_var,
            ab_triage_probe: self.ab_switches.sat_ab_triage_probe.clone(),
            chc_accept_profile: self.ab_switches.chc_accept_profile,
            chc_cata_trace: self.ab_switches.chc_cata_trace,
            chc_houdini_debug: self.ab_switches.chc_houdini_debug,
            chc_imc_stats: self.ab_switches.chc_imc_stats,
            chc_proof_itp_stats: self.ab_switches.chc_proof_itp_stats,
            chc_ice_dt_trace: self.ab_switches.chc_ice_dt_trace,
            chc_dt_bmc_trace: self.ab_switches.chc_dt_bmc_trace,
            chc_v2_debug: self.ab_switches.chc_v2_debug,
            chc_ground_bt_debug: self.ab_switches.chc_ground_bt_debug,
            chc_bmc_nested_debug: self.ab_switches.chc_bmc_nested_debug,
            chc_debug_marker_dag_verify: self.ab_switches.chc_debug_marker_dag_verify,
            chc_array_frontier_telemetry: self.ab_switches.chc_array_frontier_telemetry,
            chc_cata_dump_abstract: self.ab_switches.chc_cata_dump_abstract.clone(),
            chc_cata_dump_obligations: self.ab_switches.chc_cata_dump_obligations.clone(),
            chc_dump_scalarized: self.ab_switches.chc_dump_scalarized.clone(),
            chc_dump_failed_replay_obligation: self
                .ab_switches
                .chc_dump_failed_replay_obligation
                .clone(),
            chc_checksat_dump: self.ab_switches.chc_checksat_dump.clone(),
            chc_pdr_dump: self.ab_switches.chc_pdr_dump.clone(),
            chc_proof_itp_dump: self.ab_switches.chc_proof_itp_dump.clone(),
            chc_checksat_trace: self.ab_switches.chc_checksat_trace,
            euf_gap_stats: self.ab_switches.euf_gap_stats,
            lia_instrument: self.ab_switches.lia_instrument,
            probe_stats_every: self.ab_switches.probe_stats_every,
            str_nf_closures: self.ab_switches.str_nf_closures.clone(),
            trace_cegqi_attr: self.ab_switches.trace_cegqi_attr,
            debug_read_pin: self.ab_switches.debug_read_pin,
            f1_diag: self.ab_switches.f1_diag,
            census_trace: self.ab_switches.census_trace,
            debug_pigeonhole: self.ab_switches.debug_pigeonhole,
            cert_debug: self.ab_switches.cert_debug,
            count_debug: self.ab_switches.count_debug,
            tseitin_trace: self.ab_switches.tseitin_trace,
            debug_subst: self.ab_switches.debug_subst,
            debug_split_exit: self.ab_switches.debug_split_exit,
            debug_class_merge: self.ab_switches.debug_class_merge,
            milp_fastpath_debug: self.ab_switches.milp_fastpath_debug,
            demand_debug: self.ab_switches.demand_debug,
            prop_debug: self.ab_switches.prop_debug,
            quant_stats: self.ab_switches.quant_stats,
            debug_fixup: self.ab_switches.debug_fixup,
            debug_cegar: self.ab_switches.debug_cegar,
            str_prepass_stats: self.ab_switches.str_prepass_stats,
            milp_lane_trace: self.ab_switches.milp_lane_trace,
            verify_mixed_strings_stats: self.ab_switches.verify_mixed_strings_stats,
            a5_uf_eq_defer: self.ab_switches.a5_uf_eq_defer,
            spike_dump: self.ab_switches.spike_dump,
            spike_verbose: self.ab_switches.spike_verbose,
            qfax_combiner_route: self.ab_switches.qfax_combiner_route,
            qfax_cegar: self.ab_switches.qfax_cegar,
            qfax_lanes_debug: self.ab_switches.qfax_lanes_debug,
            probe_strict_check: self.ab_switches.probe_strict_check,
            probe_cert_reject: self.ab_switches.probe_cert_reject,
            uflia_witness_debug: self.ab_switches.uflia_witness_debug,
            pb_sym_debug: self.ab_switches.pb_sym_debug,
            pb_farkas_cert: self.ab_switches.pb_farkas_cert,
            qfax_neg_eq_witness: self.ab_switches.qfax_neg_eq_witness,
            qfax_neg_chain_gate: self.ab_switches.qfax_neg_chain_gate,
            vsids_decay: self.ab_switches.vsids_decay,
            inprobe_mult: self.ab_switches.inprobe_mult,
            factor_elim_bound: self.ab_switches.factor_elim_bound,
            pb_sls_endgame_threshold: self.ab_switches.pb_sls_endgame_threshold,
            dump_query_dir: self.ab_switches.dump_query_dir.clone(),
            keep_alethe_artifacts: self.ab_switches.keep_alethe_artifacts,
            no_quant_unit_authority: self.ab_switches.no_quant_unit_authority,
            no_skolem_witness_sat: self.ab_switches.no_skolem_witness_sat,
            no_consequence_replay: self.ab_switches.no_consequence_replay,
            vacuous_marker_narrow: self.ab_switches.vacuous_marker_narrow,
            proj_axiom_budget: self.ab_switches.proj_axiom_budget,
            uflia_witness_complete: self.ab_switches.uflia_witness_complete,
            uflia_witness_parts: self.ab_switches.uflia_witness_parts.clone(),
            uflia_fused_detour: self.ab_switches.uflia_fused_detour,
            verify_memo: self.ab_switches.verify_memo,
            pb_eqagg_debug: self.ab_switches.pb_eqagg_debug,
            pb_bnb: self.ab_switches.pb_bnb,
            no_pb_sls_feasfirst: self.ab_switches.no_pb_sls_feasfirst,
            pb_strict_optimum: self.ab_switches.pb_strict_optimum,
            pb_sls_unified: self.ab_switches.pb_sls_unified,
            pb_proof_tap_soft_cap_mib: self.ab_switches.pb_proof_tap_soft_cap_mib,
            sls_planted: self.ab_switches.sls_planted,
            sls_sweep: self.ab_switches.sls_sweep,
            oll_file: self.ab_switches.oll_file.clone(),
            oll_expect: self.ab_switches.oll_expect.clone(),
            pb_debug_panic_on_incumbent: self.ab_switches.pb_debug_panic_on_incumbent,
            sat_prune_conflict_experiments: self.ab_switches.sat_prune_conflict_experiments,
            debug_lazy_sync: self.ab_switches.debug_lazy_sync,
            debug_fc_sync: self.ab_switches.debug_fc_sync,
            lra_warm_stats: self.ab_switches.lra_warm_stats,
            fuzz_verbose: self.ab_switches.fuzz_verbose,
            certora_trace: self.ab_switches.certora_trace,
            debug_abv_finite_array: self.ab_switches.debug_abv_finite_array,
            debug_abv_packed_lookup: self.ab_switches.debug_abv_packed_lookup,
            debug_ladder: self.ab_switches.debug_ladder,
            debug_wgr: self.ab_switches.debug_wgr,
            debug_completion_merge: self.ab_switches.debug_completion_merge,
            debug_arith_oracle: self.ab_switches.debug_arith_oracle,
            debug_unwitnessed: self.ab_switches.debug_unwitnessed,
            cut_trace: self.ab_switches.cut_trace,
            dump_render: self.ab_switches.dump_render,
            chc_array_tree_refutation: self.ab_switches.chc_array_tree_refutation,
            chc_dont_care_filter: self.ab_switches.chc_dont_care_filter,
            chc_intern: self.ab_switches.chc_intern,
            chc_array_inv: self.ab_switches.chc_array_inv,
            chc_dt_recursive_prefix: self.ab_switches.chc_dt_recursive_prefix,
            interface_diet: self.ab_switches.interface_diet.clone(),
            bv_preprocess: self.ab_switches.bv_preprocess.clone(),
            fc_cegar_iters: self.ab_switches.fc_cegar_iters,
            int_pigeonhole_enrich_k: self.ab_switches.int_pigeonhole_enrich_k,
            ext_row_seed: self.ab_switches.ext_row_seed,
            debug_row_seed: self.ab_switches.debug_row_seed,
            dpll_mint_theory_vars: self.ab_switches.dpll_mint_theory_vars,
            dpll_ite_lift: self.ab_switches.dpll_ite_lift,
            euf_bool_arg_repair: self.ab_switches.euf_bool_arg_repair,
            lra_warm_theory: self.ab_switches.lra_warm_theory,
            force_array_euf: self.ab_switches.force_array_euf,
            ab_maxsat_core_clause: self.ab_switches.ab_maxsat_core_clause,
            ab_maxsat_descent_organic_slice: self.ab_switches.ab_maxsat_descent_organic_slice,
            ab_maxsat_kick_gap_abs: self.ab_switches.ab_maxsat_kick_gap_abs,
            ab_maxsat_descent_kick_scale: self.ab_switches.ab_maxsat_descent_kick_scale,
            uflia_arith_decisions: self.ab_switches.uflia_arith_decisions,
        };
        let _ = ay_core::set_global_misc_cli_flags(flags);
    }

    /// Install the SAT A/B opt-outs once before any solve (B26).
    fn install_sat_ab_switches(&self) {
        let f = &self.ab_switches;
        let switches = ay_core::SatAbSwitches {
            no_bve_inst_gate: f.sat_no_bve_inst_gate,
            no_bve_sparse_deep: f.sat_no_bve_sparse_deep,
            no_dense_skip_lift: f.sat_no_dense_skip_lift,
            no_factor_bin_fastpath: f.sat_no_factor_bin_fastpath,
            no_factor_dense: f.sat_no_factor_dense,
            no_factor_dense_init: f.sat_no_factor_dense_init,
            no_probe_route: f.sat_no_probe_route,
            no_aggressive_route: f.sat_no_aggressive_route,
            no_bve_sparse: f.sat_no_bve_sparse,
            no_bve_post_collapse: f.sat_no_bve_post_collapse,
            no_subst_auto: f.sat_no_subst_auto,
            subst_auto_uncapped: f.sat_subst_auto_uncapped,
            no_drat_subst: f.sat_no_drat_subst,
            bve_additive_fastelim: f.sat_bve_additive_fastelim,
            no_bve_additive_fastelim: f.sat_no_bve_additive_fastelim,
            no_lucky: f.sat_no_lucky,
            no_midband_deep_restart: f.sat_no_midband_deep_restart,
            no_orbitope: f.sat_no_orbitope,
            no_orbitope_alo_columns: f.sat_no_orbitope_alo_columns,
            no_symmetry_sr_auxfree: f.sat_no_symmetry_sr_auxfree,
            mode_equiticks: f.sat_mode_equiticks,
            eqt_progress: f.sat_eqt_progress,
            congruence_memory_bound: f.sat_congruence_memory_bound,
            circuit_equiv_throughput_profile: f.sat_circuit_equiv_throughput_profile,
            signed_symmetry: f.sat_signed_symmetry,
            signed_symmetry_sr: f.sat_signed_symmetry_sr,
            composite_symmetry: f.sat_composite_symmetry,
            symmetry_sr: f.sat_symmetry_sr,
            symmetry_hhw: f.sat_symmetry_hhw,
            bve_sparse_max_vars: f.sat_bve_sparse_max_vars,
            bve_sparse_max_density: f.sat_bve_sparse_max_density,
            deterministic_inproc: f.sat_deterministic_inproc,
            congruence_parity_trust: f.sat_congruence_parity_trust,
        };
        if switches != ay_core::SatAbSwitches::default() {
            let _ = ay_core::set_global_sat_ab_switches(switches);
        }
    }

    /// Install CLI-owned theory feature switches before executor construction.
    fn install_theory_disable_flags(&self) {
        let max_fixpoint_rounds = self
            .max_fixpoint_rounds
            .map(|rounds| rounds as usize)
            .filter(|&rounds| rounds > 0);
        let flags = ay_core::TheoryDisableFlags {
            no_bound_axioms: self.no_bound_axioms,
            no_theory_propagation: self.no_theory_propagation,
            no_bcp_theory_check: self.no_bcp_theory_check,
            no_ite_deferral: self.no_ite_deferral,
            disable_theory_check: false,
            no_inline_lemmas: self.no_inline_lemmas,
            no_implied_bounds: self.no_implied_bounds,
            no_bound_refinement: self.no_bound_refinement,
            no_bcp_implied_restraint: self.no_bcp_implied_restraint,
            max_fixpoint_rounds,
            no_nia_clausal_sls: self.ab_switches.no_nia_clausal_sls,
            no_lra_warm_simplex: self.ab_switches.no_lra_warm_simplex,
            no_euf_inc_diseq_undo: self.ab_switches.no_euf_inc_diseq_undo,
            no_euf_lazy_explain: self.ab_switches.no_euf_lazy_explain,
            no_euf_lazy_noprop: self.ab_switches.no_euf_lazy_noprop,
            no_lia_probe_scan: self.ab_switches.no_lia_probe_scan,
            no_lra_fast_decision: self.ab_switches.no_lra_fast_decision,
            no_we_s1: self.ab_switches.no_we_s1,
            no_euf_inc_cong_undo: self.ab_switches.no_euf_inc_cong_undo,
            no_lra_shortest_poly: self.ab_switches.no_lra_shortest_poly,
            no_enum_sat: self.ab_switches.no_enum_sat,
            no_uc_minimize: self.ab_switches.no_uc_minimize,
            disable_phase_epoch_skip: self.ab_switches.disable_phase_epoch_skip,
            no_const_interp_cert: self.ab_switches.no_const_interp_cert,
            no_abvfp_flatten: self.ab_switches.dpll_no_abvfp_flatten,
            no_closed_sentence_cert: self.ab_switches.dpll_no_closed_sentence_cert,
            no_dt_uflia: self.ab_switches.dpll_no_dt_uflia,
            no_dt_d1: self.ab_switches.dpll_no_dt_d1,
            no_euf_lnh: self.ab_switches.dpll_no_euf_lnh,
            no_idl_engine: self.ab_switches.dpll_no_idl_engine,
            no_int_coloring: self.ab_switches.dpll_no_int_coloring,
            no_int_pigeonhole: self.ab_switches.dpll_no_int_pigeonhole,
            no_lnh_leastidx: self.ab_switches.dpll_no_lnh_leastidx,
            no_lra_inc_engine: self.ab_switches.dpll_no_lra_inc_engine,
            no_lra_inc_engine_full: self.ab_switches.dpll_no_lra_inc_engine_full,
            no_lra_inc_warm: self.ab_switches.dpll_no_lra_inc_warm,
            no_nested_array_residue_rescue: self.ab_switches.dpll_no_nested_array_residue_rescue,
            no_prop_feedback: self.ab_switches.dpll_no_prop_feedback,
            no_uc_lia_probe_fallthrough: self.ab_switches.dpll_no_uc_lia_probe_fallthrough,
            no_uc_minimize_general: self.ab_switches.dpll_no_uc_minimize_general,
            force_qfax_arr_bcp_lanes: self.ab_switches.dpll_force_qfax_arr_bcp_lanes,
            no_rdl_engine: self.ab_switches.dpll_no_rdl_engine,
            no_str_p2: self.ab_switches.dpll_no_str_p2,
            no_str_p3: self.ab_switches.dpll_no_str_p3,
            no_str_w4: self.ab_switches.dpll_no_str_w4,
            no_str_w5: self.ab_switches.dpll_no_str_w5,
            no_str_w6: self.ab_switches.dpll_no_str_w6,
            no_str_w7: self.ab_switches.dpll_no_str_w7,
            no_str_witness: self.ab_switches.dpll_no_str_witness,
        };
        let _ = ay_core::set_global_theory_disable_flags(flags);
    }

    /// Install the CHC switch set once before selecting a solve route.
    pub(super) fn install_chc_ab_switches(&self) {
        let flags = &self.ab_switches;
        let switches = ay_chc::ab_switches::ChcAbSwitches {
            deriv_expansion: !flags.chc_no_deriv_expansion,
            early_safety_check: !flags.chc_no_early_safety_check,
            ground_witness: !flags.chc_no_ground_witness,
            diseq_swap: !flags.chc_no_diseq_swap,
            fwdsim_fix: !flags.chc_no_fwdsim_fix,
            guarded_impl_hints: !flags.chc_no_guarded_impl_hints,
            houdini_phaseb_fast: !flags.chc_no_houdini_phaseb_fast,
            dt_bmc_elim: !flags.chc_no_dt_bmc_elim,
            bitblast_dynamic_abort: !flags.chc_no_bitblast_dynamic_abort,
            bmc_multipred_ts: !flags.chc_no_bmc_multipred_ts,
            bmc_ts_incremental: !flags.chc_no_bmc_ts_incremental,
            array_store_forwarding: !flags.chc_no_array_store_forwarding,
            cata_elements: !flags.chc_no_cata_elements,
            ground_backtranslation: !flags.chc_no_ground_backtranslation,
            ground_table_concretization: !flags.chc_no_ground_table_concretization,
            houdini_bv: !flags.chc_no_houdini_bv,
            pc_split: !flags.chc_no_pc_split,
            split_sym: !flags.chc_no_split_sym,
            word_bv: !flags.chc_no_word_bv,
            may_pob: !flags.chc_no_may_pob,
            exec_dv_retry: !flags.chc_no_exec_dv_retry,
            exec_unknown_memo: !flags.chc_no_exec_unknown_memo,
            front_probe_clamp: !flags.chc_no_front_probe_clamp,
            graph_collapse: !flags.chc_no_graph_collapse,
            houdini_disjunctive: !flags.chc_no_houdini_disjunctive,
            houdini_stage5: !flags.chc_no_houdini_stage5,
            imc_proof_itp: !flags.chc_no_imc_proof_itp,
            pdr_lemma_sanitize: !flags.chc_no_pdr_lemma_sanitize,
            tpa_fixpoint: !flags.chc_no_tpa_fixpoint,
            array_relational: !flags.chc_no_array_relational,
            array_relational_v2: !flags.chc_no_array_relational_v2,
            dt_bmc: !flags.chc_no_dt_bmc,
            qual_mine: !flags.chc_no_qual_mine,
            qual_mixed: !flags.chc_no_qual_mixed,
            cata_route: !flags.chc_no_cata,
            cata_v2: !flags.chc_no_cata_v2,
            condense: !flags.chc_no_condense,
        };
        if switches != ay_chc::ab_switches::ChcAbSwitches::default() {
            let _ = ay_chc::ab_switches::set(switches);
        }
    }
}
