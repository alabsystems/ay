// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the LIA (Linear Integer Arithmetic) solver.

use super::*;
use ay_core::assert_conflict_soundness;
use ay_core::term::{TermId, TermStore};

mod affine_min_core;
mod affine_rref_hoist;
mod augment_shared_reasons;
mod bench_loop_b;
mod bounds_view_equivalence;
mod core_solver;
mod dioph_fold_cache;
mod int_bounds_dirty;
mod justified_bounds;
mod lattice_refute;
mod linear_parse_cache_carry;
mod modular;
mod modular_conflict_polarity;
mod nonintegral_constant_rows;
mod offset_propagation;
mod perf_hot_loop;
mod probe_hypothesis_premise;
mod rational;
mod sent_equality_closure;
mod verification;
