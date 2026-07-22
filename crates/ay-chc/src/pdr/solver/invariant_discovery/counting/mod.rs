// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Counting, three-variable difference bound, and multi-linear invariant discovery.

use super::super::{InductiveCheckResult, PdrSolver};
use crate::pdr::frame::Lemma;
use crate::smt::SmtResult;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

mod counting_core;
mod counting_extract;
mod multi_linear;
mod same_delta_diff;
mod three_var_diff;
mod three_var_diff_extract;
