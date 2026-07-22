// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ITE toggle bounds, ITE constant propagation, and lemma hint application.

use super::super::super::PdrSolver;
use crate::pdr::frame::Lemma;
use crate::smt::{SmtResult, SmtValue};
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, PredicateId};

mod constant_propagation;
mod lemma_hints;
mod toggle_bounds;
