// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

pub(super) use super::*;
pub(super) use crate::solver::preprocess::ModelViolation;

mod benchmarks;
mod bve_constraint_heavy;
mod bve_reconstruction_e2e;
mod component_analysis;
mod congruence;
mod decompose_lrat;
mod decompose_rewrite;
mod deduplicate_proof;
mod diagnostic_trace;
mod domain_restriction;
mod domain_restriction_bucket_queue;
mod ext_restart_arena_rebuild;
mod flip_to_none;
mod ic3_clause_category;
mod ic3_domain_expansion_8806;
mod ic3_state_persistence;
mod ic3_stress;
mod incremental;
mod inprocessing;
mod inprocessing_large_formula_gate;
mod instantiate;
mod kitten;
mod lifecycle;
mod lookahead;
mod minimize;
mod observer;
mod original_clause_ledger;
mod otfs_bve_occ;
mod oversized_clause_split;
mod phase_hints;
mod preprocess_transaction_ledger;
mod preprocessing_bve;
mod proof_checking;
mod proof_lrat;
mod propagation;
#[cfg(feature = "raw-pointer-bcp")]
mod propagation_bcp_unsafe;
mod pushpop_leak_fuzz;
mod reason_marks;
mod reconstruction;
mod reduction;
mod reduction_schedule;
mod rephase;
mod restart;
mod scoped_bve_pop_soundness;
mod scoped_bve_var_reuse_false_verdict;
mod search;
mod soundness;
mod statistics;
mod subsumption;
mod support;
mod symmetry;
mod theory;
mod vivification;

use support::*;
