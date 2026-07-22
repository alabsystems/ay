// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bitvector operations for AY Solver API.

use super::types::{SolverError, Term};
use super::Solver;

mod arithmetic;
mod bitwise;
mod comparison;
mod conversion;
mod division;
mod extract_concat;
mod overflow;
mod rotate_repeat;
mod shift;
