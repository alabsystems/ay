// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the LIA (Linear Integer Arithmetic) solver.

use super::*;
use ay_core::assert_conflict_soundness;
use ay_core::term::{TermId, TermStore};

mod affine_min_core;
mod augment_shared_reasons;
mod bench_loop_b;
mod bounds_view_equivalence;
mod core_solver;
mod int_bounds_dirty;
mod modular;
mod perf_hot_loop;
mod probe_quickxplain;
mod rational;
mod verification;
