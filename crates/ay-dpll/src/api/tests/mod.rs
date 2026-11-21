// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Tests use the deprecated panicking convenience API; migration tracked in ay#6183.
#![allow(deprecated)]

/// Reuse the pinned whole-document checker and its invalid-empty-reflexivity
/// control across crate-internal source-candidate regressions.
pub(crate) fn check_paired_document_for_test(problem: &str, proof: &str) {
    test_native_datatype_batch::check_whole_paired_document(
        problem,
        proof,
        &crate::api::CarcaraSurface::Supported,
    );
}

mod test_abduction;
mod test_annotated_core;
mod test_api_health;
mod test_array_ext_witness_api;
mod test_bool_eq;
mod test_bv;
mod test_bv_api_simplification;
mod test_bv_quantifier;
mod test_closure_capture_model;
mod test_competition_api_guard;
mod test_core;
mod test_counterexample_minimization;
mod test_datatype_tester_spellings;
mod test_declaration_identity;
mod test_define_fun;
mod test_empty_identity_bundle;
mod test_exact_query_bundle;
mod test_explanation_report;
mod test_fp;
mod test_fp_bv_bridge;
mod test_incremental_cegis;
mod test_incremental_proof;
mod test_int2bv_roundtrip_bridge;
mod test_interpolation_spike;
mod test_lemma_persistence;
mod test_maxsmt;
mod test_model_access;
mod test_model_minimize;
mod test_model_parse_fp_dt;
mod test_model_value_display_seq;
mod test_native_assertion_source;
mod test_native_assertion_source_binders;
mod test_native_assertion_source_elaborated;
mod test_native_bv_assumption_proofs;
mod test_native_datatype_batch;
mod test_native_opaque_sort;
mod test_native_owned_constant;
mod test_native_owned_function;
mod test_native_owned_function_bounded;
mod test_native_replay;
mod test_native_replay_identity_scope;
mod test_native_replay_qf_ufbvlia;
mod test_native_replay_transport;
mod test_native_seq_empty;
mod test_native_sequence_operations;
mod test_overloaded_ctor_model;
mod test_periodic_int_array_model;
mod test_proof_access;
mod test_proof_artifact;
mod test_query_dump;
mod test_seq_owned_datatype;
mod test_solver_scope;
mod test_solving_assumptions;
mod test_solving_controls;
mod test_string_bv_bridge;
mod test_strings;
mod test_term_inspection;
mod test_trust_bool_iff_refutation;
mod test_trust_consumer;
mod test_trust_wrapping_refutation;
mod test_try_check_sat;
mod test_type_logic;
mod test_type_model_value;
mod test_unsat_core;
mod test_verification_consumer_conditional_mutref;
mod test_verification_consumer_popcount_reducer;
mod test_verification_consumer_scaled_relational_exit;
mod test_verification_consumer_seq_carrier;

mod test_verification_consumer_nullary_constructor;
mod test_verification_consumer_proportional_equality;

mod test_native_sort_inspection;
