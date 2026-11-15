// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::assert_conflict_soundness;
use ay_core::Sort;

mod axiom_premises;
mod const_default_chain;
mod core_solver;
mod external_eq_report;
mod guarded_row2_lifecycle;
mod interface_eq;
mod propagation_idempotence;
mod select_map_antecedents;
mod store_chain;
mod store_chain_classes;
mod store_chain_provenance;
mod store_target_8785;
mod verification;
mod weak_equiv;
mod weak_lemmas;

fn make_array_sort() -> Sort {
    Sort::array(Sort::Int, Sort::Int)
}

mod row2_applied_ack;
