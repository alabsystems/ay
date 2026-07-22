// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Parity invariant discovery: modular arithmetic invariants and expression helpers.

use super::super::PdrSolver;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, PredicateId};

mod analysis;
mod conditional_threshold;
mod core;
mod increment;
mod toggle;
