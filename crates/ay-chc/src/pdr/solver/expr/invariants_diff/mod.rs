// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Difference invariant discovery.
//!
//! Scaled-difference invariants are in `invariants_scaled_diff.rs`.

use super::super::PdrSolver;
use crate::pdr::config::InitIntBounds;
use crate::smt::SmtResult;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, HornClause, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use std::sync::Arc;

mod discovery;
mod entry_values;
mod preservation;

#[cfg(test)]
mod tests;
