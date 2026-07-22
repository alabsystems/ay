// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sum, triple-sum, and scaled-sum invariant discovery.

use super::super::PdrSolver;
use crate::smt::SmtResult;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;

mod sum_scaled;
mod sum_signed_triple;
mod sum_triple;
mod sum_triple_verify;
mod sum_two_var;

#[cfg(test)]
mod tests;
