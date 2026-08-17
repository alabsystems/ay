// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Theory-layer CLI disable flags.

/// Centralized theory-layer disable flags.
///
/// A single struct set once from the CLI `--no-*` / `--max-fixpoint-rounds`
/// flags and cached for the process lifetime.
#[derive(Debug, Clone, Default)]
pub struct TheoryDisableFlags {
    /// `--no-bound-axioms`
    pub no_bound_axioms: bool,
    /// `--no-theory-propagation`
    pub no_theory_propagation: bool,
    /// `--no-bcp-theory-check`
    pub no_bcp_theory_check: bool,
    /// `--no-ite-deferral`
    pub no_ite_deferral: bool,
    /// `--disable=theory-check`
    pub disable_theory_check: bool,
    /// `--no-inline-lemmas`
    pub no_inline_lemmas: bool,
    /// `--no-implied-bounds`
    pub no_implied_bounds: bool,
    /// `--no-bound-refinement`
    pub no_bound_refinement: bool,
    /// `--no-bcp-implied-restraint` — kill switch for the sat-side-model-search
    /// Fix #2 restraint (single-pass BCP implied bounds on the
    /// propagation-disabled cex lane). When set, BCP-time implied-bounds
    /// computation reverts to the full fixpoint cascade.
    pub no_bcp_implied_restraint: bool,
    /// `--max-fixpoint-rounds=N`
    pub max_fixpoint_rounds: Option<usize>,
    /// `--no-nia-clausal-sls` — quarantine the NIA clausal local-search lane
    /// (B16: was the never-set AY_NIA_NO_CLAUSAL_SLS env var).
    pub no_nia_clausal_sls: bool,
    /// `--no-lra-warm-simplex` — disable cross-solve warm simplex state
    /// (B16: was the never-set LRA warm-simplex env spelling).
    pub no_lra_warm_simplex: bool,
    /// `--no-enum-sat` — disable the enum finite-domain SAT lane (B17).
    pub no_enum_sat: bool,
    /// `--no-euf-inc-diseq-undo` — disable the incremental disequality-undo
    /// lane (B30: was the never-set --no-euf-inc-diseq-undo opt-out).
    pub no_euf_inc_diseq_undo: bool,
    /// `--no-euf-lazy-explain` — restore eager propagation reasons (B30).
    pub no_euf_lazy_explain: bool,
    /// `--no-euf-lazy-noprop` — disable lazy no-propagation reasons (B30).
    pub no_euf_lazy_noprop: bool,
    /// `--no-lia-probe-scan` — skip the LIA probe minimization scan (B30).
    pub no_lia_probe_scan: bool,
    /// `--no-lra-fast-decision` — force the legacy decision-suggestion scan
    /// (B30).
    pub no_lra_fast_decision: bool,
    /// `--no-we-s1` — disable the S1 word-equation regex lane (B30).
    pub no_we_s1: bool,
    /// `--no-euf-inc-cong-undo` — disable the incremental congruence-undo
    /// lane (B36).
    pub no_euf_inc_cong_undo: bool,
    /// `--no-lra-shortest-poly` — restore the Z3/Dantzig most-violated
    /// leaving-variable rule (B36).
    pub no_lra_shortest_poly: bool,
    /// `--no-uc-minimize` — restore padded-superset unsat cores (B17).
    pub no_uc_minimize: bool,
    /// `--disable-phase-epoch-skip` — restore the unconditional O(atoms)
    /// phase re-seed (B17).
    pub disable_phase_epoch_skip: bool,
    /// `--no-const-interp-cert` — disable the constant-interpretation
    /// certificate gate (B17; the diagnostic shadow mode retired with the
    /// env var, unmeasured).
    pub no_const_interp_cert: bool,
    /// B28 dpll lane opt-outs (each replaces a never-set default-on env).
    pub no_abvfp_flatten: bool,
    /// `--dpll-no-closed-sentence-cert`
    pub no_closed_sentence_cert: bool,
    /// `--dpll-no-dt-uflia`
    pub no_dt_uflia: bool,
    /// `--dpll-no-dt-d1`
    pub no_dt_d1: bool,
    /// `--dpll-no-euf-lnh`
    pub no_euf_lnh: bool,
    /// `--dpll-no-idl-engine`
    pub no_idl_engine: bool,
    /// `--dpll-no-int-coloring`
    pub no_int_coloring: bool,
    /// `--dpll-no-int-pigeonhole`
    pub no_int_pigeonhole: bool,
    /// `--dpll-no-lnh-leastidx`
    pub no_lnh_leastidx: bool,
    /// `--dpll-no-lra-inc-engine`
    pub no_lra_inc_engine: bool,
    /// `--dpll-no-lra-inc-engine-full`
    pub no_lra_inc_engine_full: bool,
    /// `--dpll-no-lra-inc-warm`
    pub no_lra_inc_warm: bool,
    /// `--dpll-no-nested-array-residue-rescue`
    pub no_nested_array_residue_rescue: bool,
    /// `--dpll-no-prop-feedback`
    pub no_prop_feedback: bool,
    /// `--dpll-no-uc-lia-probe-fallthrough`
    pub no_uc_lia_probe_fallthrough: bool,
    /// `--dpll-no-uc-minimize-general`
    pub no_uc_minimize_general: bool,
    /// `--dpll-force-qfax-arr-bcp-lanes`
    pub force_qfax_arr_bcp_lanes: bool,
    /// `--dpll-no-rdl-engine`
    pub no_rdl_engine: bool,
    /// `--dpll-no-str-p2`
    pub no_str_p2: bool,
    /// `--dpll-no-str-p3`
    pub no_str_p3: bool,
    /// `--dpll-no-str-w4`
    pub no_str_w4: bool,
    /// `--dpll-no-str-w5`
    pub no_str_w5: bool,
    /// `--dpll-no-str-w6`
    pub no_str_w6: bool,
    /// `--dpll-no-str-w7`
    pub no_str_w7: bool,
    /// `--dpll-no-str-witness`
    pub no_str_witness: bool,
}
