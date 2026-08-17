// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::executor_types::SolveResult;
use crate::Executor;
use ay_frontend::parse;

// M-A2 lazy-persistent-combiner shadow differential. The module is itself
// `#![cfg(debug_assertions)]`, so it is absent from release test builds (where
// the shadow does not exist).
mod array_declared_witness;
#[cfg(debug_assertions)]
mod array_persistent_combiner_shadow;
mod bv_lia_indep_model_graft;
mod qf_auflia;
mod qf_auflia_l3_propagation;
mod qf_auflra_and_regression;
mod qf_ax;
mod qf_eia;
mod qf_lia;
mod qf_lra;
mod qf_uflia;
mod qf_uflra;
