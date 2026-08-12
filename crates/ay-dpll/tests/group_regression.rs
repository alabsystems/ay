// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Consolidated regression integration tests for ay-dpll.
//! Groups 15 test modules into a single binary to reduce link time.

#![allow(clippy::panic)]

mod common;

#[path = "group_regression/boolarg_orphan_model_gate_gap.rs"]
mod boolarg_orphan_model_gate_gap;
#[path = "group_regression/bv_ite_bool_model_soundness.rs"]
mod bv_ite_bool_model_soundness;
#[path = "group_regression/combined_assumption_sat_canaries_6731.rs"]
mod combined_assumption_sat_canaries_6731;
#[path = "group_regression/combined_check_sat_assuming.rs"]
mod combined_check_sat_assuming;
#[path = "group_regression/combined_minimize_counterexamples_6731.rs"]
mod combined_minimize_counterexamples_6731;
#[path = "group_regression/false_unsat_20var_bb.rs"]
mod false_unsat_20var_bb;
#[path = "group_regression/false_unsat_6242.rs"]
mod false_unsat_6242;
#[path = "group_regression/false_unsat_array_ite_store_index.rs"]
mod false_unsat_array_ite_store_index;
#[path = "group_regression/false_unsat_auflia_disjunct_forall.rs"]
mod false_unsat_auflia_disjunct_forall;
#[path = "group_regression/false_unsat_auflia_exists_eq.rs"]
mod false_unsat_auflia_exists_eq;
#[path = "group_regression/false_unsat_auflia_rodin.rs"]
mod false_unsat_auflia_rodin;
#[path = "group_regression/false_unsat_large_coeff_ite.rs"]
mod false_unsat_large_coeff_ite;
#[path = "group_regression/false_unsat_to_int_mod_hnf.rs"]
mod false_unsat_to_int_mod_hnf;
#[path = "group_regression/farkas_degradation_tests.rs"]
mod farkas_degradation_tests;
#[path = "group_regression/issue4701_substr_splice_regression.rs"]
mod issue4701_substr_splice_regression;
#[path = "group_regression/issue_6481_implication_antecedent.rs"]
mod issue_6481_implication_antecedent;
#[path = "group_regression/unbounded_oscillation_1836.rs"]
mod unbounded_oscillation_1836;
#[path = "group_regression/validate_model_5488.rs"]
mod validate_model_5488;
#[path = "group_regression/validate_model_dag_perf.rs"]
mod validate_model_dag_perf;
#[path = "group_regression/verification_consumer_int_div_6165.rs"]
mod verification_consumer_int_div_6165;
#[path = "group_regression/verification_consumer_sum_first_n_9048.rs"]
mod verification_consumer_sum_first_n_9048;
#[path = "group_regression/verification_consumer_uninterpreted_sort_equality_8971.rs"]
mod verification_consumer_uninterpreted_sort_equality_8971;
#[path = "group_regression/zero_checked_validation_5488.rs"]
mod zero_checked_validation_5488;
