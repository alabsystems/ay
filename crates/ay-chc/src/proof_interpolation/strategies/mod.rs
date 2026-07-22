// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Interpolation strategy functions.

mod a_side_equality;
mod a_side_farkas;
mod b_combinations;
mod relaxed;
mod synthetic;

pub(crate) use a_side_equality::try_a_side_equality_interpolant;
pub(crate) use a_side_farkas::try_a_side_farkas_projection;
pub(crate) use b_combinations::{try_b_pure_combination, try_split_literals_combination};
pub(crate) use relaxed::{try_per_clause_interpolation, try_relaxed_b_origin_combination};
pub(crate) use synthetic::try_synthetic_decomposed_farkas;
