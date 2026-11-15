// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bitvector theory tests - QF_BV (pure bitvectors), QF_ABV (arrays of BV),
//! QF_UFBV (UF with BV), QF_AUFBV (arrays + UF + BV)

use crate::Executor;
use ay_frontend::parse;

mod qf_abv;
mod qf_abv_bool_range;
mod qf_aufbv;
mod qf_aufbv_fc_audit_retry;
mod qf_aufbv_forced_definition;
mod qf_aufbv_gap_completion;
mod qf_aufbv_ground_array_equality;
mod qf_aufbv_model_completeness;
mod qf_aufbv_nested_select_scan;
mod qf_bv;
mod qf_bv_division;
mod qf_ufbv;
mod regression;
