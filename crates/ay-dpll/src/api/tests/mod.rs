// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Tests use the deprecated panicking convenience API; migration tracked in ay#6183.
#![allow(deprecated)]

mod test_abduction;
mod test_annotated_core;
mod test_api_health;
mod test_array_ext_witness_api;
mod test_bool_eq;
mod test_bv;
mod test_bv_api_simplification;
mod test_bv_quantifier;
mod test_closure_capture_model;
mod test_core;
mod test_counterexample_minimization;
mod test_define_fun;
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
mod test_native_replay;
mod test_proof_access;
mod test_proof_artifact;
mod test_query_dump;
mod test_solver_scope;
mod test_solving_assumptions;
mod test_solving_controls;
mod test_string_bv_bridge;
mod test_strings;
mod test_term_inspection;
mod test_trust_consumer;
mod test_try_check_sat;
mod test_type_logic;
mod test_type_model_value;
mod test_unsat_core;
mod test_verification_consumer_popcount_reducer;
mod test_verification_consumer_seq_carrier;
