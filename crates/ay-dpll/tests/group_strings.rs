// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Consolidated strings integration tests for ay-dpll.
//! Groups 25 test modules into a single binary to reduce link time.

#![allow(clippy::panic)]

mod common;

#[path = "group_strings/char_theory.rs"]
mod char_theory;
#[path = "group_strings/false_sat_indexof_int_var.rs"]
mod false_sat_indexof_int_var;
#[path = "group_strings/false_sat_isdigit_ground_6263.rs"]
mod false_sat_isdigit_ground_6263;
#[path = "group_strings/false_sat_str_code_6263.rs"]
mod false_sat_str_code_6263;
#[path = "group_strings/membership_through_concat.rs"]
mod membership_through_concat;
#[path = "group_strings/seq_assumptions_5994.rs"]
mod seq_assumptions_5994;
#[path = "group_strings/seq_pairwise_compat.rs"]
mod seq_pairwise_compat;
#[path = "group_strings/seq_prefixof_6035.rs"]
mod seq_prefixof_6035;
#[path = "group_strings/seq_soundness_5841.rs"]
mod seq_soundness_5841;
#[path = "group_strings/seq_theory_5841.rs"]
mod seq_theory_5841;
#[path = "group_strings/slia_bridge_contradictory_value.rs"]
mod slia_bridge_contradictory_value;
#[path = "group_strings/slia_incompleteness_6263.rs"]
mod slia_incompleteness_6263;
#[path = "group_strings/slia_recheck_3393.rs"]
mod slia_recheck_3393;
#[path = "group_strings/slia_seq_routing_6010.rs"]
mod slia_seq_routing_6010;
#[path = "group_strings/str_order.rs"]
mod str_order;
#[path = "group_strings/string_at_reduction_soundness.rs"]
mod string_at_reduction_soundness;
#[path = "group_strings/string_contains_transitivity_4052.rs"]
mod string_contains_transitivity_4052;
#[path = "group_strings/string_cycle_check_soundness_4018.rs"]
mod string_cycle_check_soundness_4018;
#[path = "group_strings/string_endpoint_empty_4055.rs"]
mod string_endpoint_empty_4055;
#[path = "group_strings/string_eq_literal_model_binding.rs"]
mod string_eq_literal_model_binding;
#[path = "group_strings/string_equivalence_guard_regression.rs"]
mod string_equivalence_guard_regression;
#[path = "group_strings/string_extf_soundness_3892.rs"]
mod string_extf_soundness_3892;
#[path = "group_strings/string_gap_completion_substr.rs"]
mod string_gap_completion_substr;
#[path = "group_strings/string_mixed_validation_escape_6326.rs"]
mod string_mixed_validation_escape_6326;
#[path = "group_strings/string_theory_verification.rs"]
mod string_theory_verification;
#[path = "group_strings/strings_benchmark_differential_contract.rs"]
mod strings_benchmark_differential_contract;
#[path = "group_strings/strings_constsplit_regression_3429.rs"]
mod strings_constsplit_regression_3429;
#[path = "group_strings/strings_distinct_extf_contract.rs"]
mod strings_distinct_extf_contract;
#[path = "group_strings/strings_fix_verification_4025.rs"]
mod strings_fix_verification_4025;
#[path = "group_strings/strings_negated_extf_commuted_contract.rs"]
mod strings_negated_extf_commuted_contract;
#[path = "group_strings/strings_proof_coverage_p5.rs"]
mod strings_proof_coverage_p5;
#[path = "group_strings/strings_prover_audit.rs"]
mod strings_prover_audit;
#[path = "group_strings/strings_soundness_gate_4025.rs"]
mod strings_soundness_gate_4025;
