// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core bound invariant discovery: orchestrators, entry guards, fact conjuncts,
//! joint bounds, expression helpers, propagation, and monotonicity checks.

use super::super::super::PdrSolver;
use crate::smt::SmtResult;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use std::collections::VecDeque;

mod difference_bounds;
mod fact_joint;
mod monotonicity;
mod orchestrator;
mod propagation;
