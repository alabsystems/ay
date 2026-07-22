// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bound assertion methods for the LRA solver.
//!
//! Split into submodules by concern:
//! - `seeded`: model-seeded propagation
//! - `assert_bounds`: core bound assertion and tightening
//! - `fixed_terms`: fixed-term representative tracking
//! - `model_equalities`: offset-equality discovery and materialization

use super::*;

mod assert_bounds;
mod fixed_terms;
mod model_equalities;
mod seeded;
