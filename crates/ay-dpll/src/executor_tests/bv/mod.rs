// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bitvector theory tests - QF_BV (pure bitvectors), QF_ABV (arrays of BV),
//! QF_UFBV (UF with BV), QF_AUFBV (arrays + UF + BV)

use crate::Executor;
use ay_frontend::parse;

mod qf_abv;
mod qf_aufbv;
mod qf_bv;
mod qf_bv_division;
mod qf_ufbv;
mod regression;
