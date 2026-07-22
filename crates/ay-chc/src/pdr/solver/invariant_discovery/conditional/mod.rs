// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Modular equality, conditional, and step-bounded difference invariant discovery.

use super::super::PdrSolver;
use crate::smt::SmtResult;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use std::sync::Arc;

mod conditional_inv;
mod linear_combination;
mod linear_combination_verify;
mod modular_equality;
mod step_bounded;
