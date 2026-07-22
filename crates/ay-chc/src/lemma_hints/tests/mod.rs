// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for lemma hint providers.

#![allow(clippy::unwrap_used)]

use super::*;

use super::bounds_from_init::BoundsFromInitProvider;
use super::mod_arithmetic::{ModResidueHintProvider, ModSumHintProvider};
use super::parametric_mul::ParametricMultiplicationProvider;
use crate::ChcOp;
use crate::ChcSort;

mod helpers_and_api;
mod infrastructure;
mod mod_hints;
mod parametric_mul_tests;
mod recurrence;
