// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Consolidated lia integration tests for ay-dpll.
//! Groups 36 test modules into a single binary to reduce link time.

#![allow(clippy::panic)]

mod common;

#[path = "group_lia/bound_axiom_injection_4919.rs"]
mod bound_axiom_injection_4919;
#[path = "group_lia/bound_refinement_4919.rs"]
mod bound_refinement_4919;
#[path = "group_lia/floor_div_mod_3959.rs"]
mod floor_div_mod_3959;
#[path = "group_lia/guarded_eq_mining_23.rs"]
mod guarded_eq_mining_23;
#[path = "group_lia/lia_all_distinct_false_unsat.rs"]
mod lia_all_distinct_false_unsat;
#[path = "group_lia/lia_check_sat_assuming_6728.rs"]
mod lia_check_sat_assuming_6728;
#[path = "group_lia/lia_convert_jpg2gif_false_unsat.rs"]
mod lia_convert_jpg2gif_false_unsat;
#[path = "group_lia/lia_cross_solver_tseitin_isolation_6853.rs"]
mod lia_cross_solver_tseitin_isolation_6853;
#[path = "group_lia/lia_disjunctive_false_unsat_6209.rs"]
mod lia_disjunctive_false_unsat_6209;
#[path = "group_lia/lia_doubling_chain_2832.rs"]
mod lia_doubling_chain_2832;
#[path = "group_lia/lia_equality_chain_2767.rs"]
mod lia_equality_chain_2767;
#[path = "group_lia/lia_equality_chain_addition_2830.rs"]
mod lia_equality_chain_addition_2830;
#[path = "group_lia/lia_incremental_bmc_stress.rs"]
mod lia_incremental_bmc_stress;
#[path = "group_lia/lia_incremental_false_unsat_6853.rs"]
mod lia_incremental_false_unsat_6853;
#[path = "group_lia/lia_incremental_guarded_shapes_6661.rs"]
mod lia_incremental_guarded_shapes_6661;
#[path = "group_lia/lia_incremental_push_pop.rs"]
mod lia_incremental_push_pop;
#[path = "group_lia/lia_incremental_routing_6661.rs"]
mod lia_incremental_routing_6661;
#[path = "group_lia/lia_ite_model_recovery_5552.rs"]
mod lia_ite_model_recovery_5552;
#[path = "group_lia/lia_mod_div_by_constant.rs"]
mod lia_mod_div_by_constant;
#[path = "group_lia/lia_model_recovery_2767.rs"]
mod lia_model_recovery_2767;
#[path = "group_lia/lia_preservation_false_sat_6214.rs"]
mod lia_preservation_false_sat_6214;
#[path = "group_lia/lia_soundness_4993.rs"]
mod lia_soundness_4993;
#[path = "group_lia/lia_transitive_equality_2737.rs"]
mod lia_transitive_equality_2737;
#[path = "group_lia/lia_unknown_recovery_4785.rs"]
mod lia_unknown_recovery_4785;
#[path = "group_lia/lira_big_m_relu_5947.rs"]
mod lira_big_m_relu_5947;
#[path = "group_lia/lira_cross_sort_soundness.rs"]
mod lira_cross_sort_soundness;
#[path = "group_lia/lira_multi_var_cross_sort.rs"]
mod lira_multi_var_cross_sort;
#[path = "group_lia/lira_to_int_5944.rs"]
mod lira_to_int_5944;
#[path = "group_lia/lira_to_int_cross_sort_6217.rs"]
mod lira_to_int_cross_sort_6217;
#[path = "group_lia/lira_to_real_only_integrality.rs"]
mod lira_to_real_only_integrality;
#[path = "group_lia/qf_lia_check_sat_assuming.rs"]
mod qf_lia_check_sat_assuming;
#[path = "group_lia/qf_lia_eager_stats_default_7894.rs"]
mod qf_lia_eager_stats_default_7894;
#[path = "group_lia/qf_lia_ite_completeness_4003.rs"]
mod qf_lia_ite_completeness_4003;
#[path = "group_lia/qflia_p0_canaries_8707.rs"]
mod qflia_p0_canaries_8707;
#[path = "group_lia/qflia_regression_8736.rs"]
mod qflia_regression_8736;
#[path = "group_lia/symbolic_mod_uf_model_gap.rs"]
mod symbolic_mod_uf_model_gap;
#[path = "group_lia/symbolic_rem_soundness.rs"]
mod symbolic_rem_soundness;
