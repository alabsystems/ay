// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Consolidated quantifiers integration tests for ay-dpll.
//! Groups 18 test modules into a single binary to reduce link time.

#![allow(clippy::panic)]

mod common;

#[path = "group_quantifiers/bounded_int_guard_soundness.rs"]
mod bounded_int_guard_soundness;

#[path = "group_quantifiers/bv_forall_uf_completion_soundness.rs"]
mod bv_forall_uf_completion_soundness;
#[path = "group_quantifiers/bv_mbqi_modelless_refutation.rs"]
mod bv_mbqi_modelless_refutation;
#[path = "group_quantifiers/cegqi_bv_uf_detection_2885.rs"]
mod cegqi_bv_uf_detection_2885;
#[path = "group_quantifiers/cegqi_ce_strip_identity.rs"]
mod cegqi_ce_strip_identity;
#[path = "group_quantifiers/cegqi_refinement_5888.rs"]
mod cegqi_refinement_5888;
#[path = "group_quantifiers/cegqi_refinement_5975.rs"]
mod cegqi_refinement_5975;
#[path = "group_quantifiers/cegqi_unknown_mapping_2879.rs"]
mod cegqi_unknown_mapping_2879;
#[path = "group_quantifiers/closed_universal_validity_precheck.rs"]
mod closed_universal_validity_precheck;
#[path = "group_quantifiers/ematching_1939.rs"]
mod ematching_1939;
#[path = "group_quantifiers/ematching_1975.rs"]
mod ematching_1975;
#[path = "group_quantifiers/ematching_deadline_break.rs"]
mod ematching_deadline_break;
#[path = "group_quantifiers/ematching_e2e_3325.rs"]
mod ematching_e2e_3325;
#[path = "group_quantifiers/ematching_multiround_3994.rs"]
mod ematching_multiround_3994;
#[path = "group_quantifiers/ematching_post_cegqi_7979.rs"]
mod ematching_post_cegqi_7979;
#[path = "group_quantifiers/finite_domain_5848.rs"]
mod finite_domain_5848;
#[path = "group_quantifiers/forall_goal_int_boundary_discharge.rs"]
mod forall_goal_int_boundary_discharge;
#[path = "group_quantifiers/frame_quantifier_instance_resolve.rs"]
mod frame_quantifier_instance_resolve;
#[path = "group_quantifiers/incremental_scope_recheck_soundness.rs"]
mod incremental_scope_recheck_soundness;
#[path = "group_quantifiers/left_inverse_attack_corpus.rs"]
mod left_inverse_attack_corpus;
#[path = "group_quantifiers/mbqi_5971.rs"]
mod mbqi_5971;
#[path = "group_quantifiers/nested_skolem_functions_7150.rs"]
mod nested_skolem_functions_7150;
#[path = "group_quantifiers/pattern_annotation_verdict_invariance.rs"]
mod pattern_annotation_verdict_invariance;
#[path = "group_quantifiers/qe_selfcheck_window_cap.rs"]
mod qe_selfcheck_window_cap;
#[path = "group_quantifiers/quantifier_alternation_soundness.rs"]
mod quantifier_alternation_soundness;
#[path = "group_quantifiers/quantifier_assertion_restore_2844.rs"]
mod quantifier_assertion_restore_2844;
#[path = "group_quantifiers/quantifier_capture_avoidance_5911.rs"]
mod quantifier_capture_avoidance_5911;
#[path = "group_quantifiers/quantifier_dpll_7150.rs"]
mod quantifier_dpll_7150;
#[path = "group_quantifiers/quantifier_model_3441.rs"]
mod quantifier_model_3441;
#[path = "group_quantifiers/quantprod_model_production.rs"]
mod quantprod_model_production;
#[path = "group_quantifiers/skolemization_5840.rs"]
mod skolemization_5840;
#[path = "group_quantifiers/ufbv_deferred_default_mode_wrong_sat.rs"]
mod ufbv_deferred_default_mode_wrong_sat;
#[path = "group_quantifiers/ufbv_deferred_selfcheck_failclosed.rs"]
mod ufbv_deferred_selfcheck_failclosed;
#[path = "group_quantifiers/ufbv_fixpoint_premise_forced_unsat.rs"]
mod ufbv_fixpoint_premise_forced_unsat;
#[path = "group_quantifiers/ufbv_fixpoint_probe_admission.rs"]
mod ufbv_fixpoint_probe_admission;
#[path = "group_quantifiers/ufbv_strict_uf_completion_coverage.rs"]
mod ufbv_strict_uf_completion_coverage;
#[path = "group_quantifiers/ufnira_uf_completion_soundness.rs"]
mod ufnira_uf_completion_soundness;
#[path = "group_quantifiers/vacuous_trigger_completeness.rs"]
mod vacuous_trigger_completeness;
