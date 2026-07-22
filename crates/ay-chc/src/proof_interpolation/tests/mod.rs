// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for proof interpolation.

#![allow(clippy::unwrap_used)]

use super::*;
use std::sync::Arc;

mod basic_and_smt_farkas;
mod farkas_projection_craig;
mod per_clause_fm;
mod proof_marking;
mod zero_farkas_lia;
