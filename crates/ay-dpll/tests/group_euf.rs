// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Consolidated euf integration tests for ay-dpll.
//! Groups 13 test modules into a single binary to reduce link time.

#![allow(clippy::panic)]

mod common;

#[path = "group_euf/euf_bool_alias_6869.rs"]
mod euf_bool_alias_6869;
#[path = "group_euf/euf_diseq_orientation_6152.rs"]
mod euf_diseq_orientation_6152;
#[path = "group_euf/euf_incremental_push_pop.rs"]
mod euf_incremental_push_pop;
#[path = "group_euf/fmap_len_lookup_min_repro.rs"]
mod fmap_len_lookup_min_repro;
#[path = "group_euf/multiarg_congruence_6154.rs"]
mod multiarg_congruence_6154;
#[path = "group_euf/uf_lia_congruence_chain_3581.rs"]
mod uf_lia_congruence_chain_3581;
#[path = "group_euf/uf_model_concrete_values_5452.rs"]
mod uf_model_concrete_values_5452;
#[path = "group_euf/ufbv_congruence_tests.rs"]
mod ufbv_congruence_tests;
#[path = "group_euf/uflia_incremental_redeclare_6813.rs"]
mod uflia_incremental_redeclare_6813;
#[path = "group_euf/uflra_false_unsat_6812.rs"]
mod uflra_false_unsat_6812;
#[path = "group_euf/uflra_incremental_push_pop.rs"]
mod uflra_incremental_push_pop;
#[path = "group_euf/ufn_assumption_soundness_6289.rs"]
mod ufn_assumption_soundness_6289;
#[path = "group_euf/ufnia_soundness_5984.rs"]
mod ufnia_soundness_5984;
#[path = "group_euf/ufnra_speculative_eq_7449.rs"]
mod ufnra_speculative_eq_7449;
