// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for PDR expression utilities.
//!
//! Extracted from expr.rs for file size management.

#![allow(clippy::unwrap_used, clippy::panic)]

use crate::pdr::config::PdrConfig;
use crate::pdr::frame::Lemma;
use crate::pdr::solver::PdrSolver;
use crate::{ChcExpr, ChcOp, ChcParser, ChcSort, ChcVar, HornClause};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::sync::Arc;

mod divisibility;
mod entry_edge;
mod interpolation;
mod kernel;
mod sampling;
mod weaken;
