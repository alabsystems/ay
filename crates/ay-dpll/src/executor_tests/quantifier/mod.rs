// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Quantifier instantiation tests - CEGQI, model-based instantiation,
//! deferred instantiations, unknown reasons

use crate::quantifier_manager::QuantifierManager;
use crate::{Executor, SolveResult, UnknownReason};
use ay_frontend::parse;

mod assuming;
mod cegqi;
mod deferred;
mod demand_lane_shadow;
mod demand_probes;
mod discharge;
mod dt_model_cert;
mod ematching;
mod finite_table_cert;
mod guard_bounded_expansion;
mod patterned_trigger_soundness;
mod prepass_reachability;
mod qe_prepass_e2e;
mod refinement;
mod unknown_and_misc;
