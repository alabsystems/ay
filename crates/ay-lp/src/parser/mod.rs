// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! MPS and CPLEX LP parsers.
//!
//! Both parsers normalize their output to [`crate::model::Problem`]. The
//! parsers are deliberately tolerant of whitespace (MPS free form) but
//! reject structurally invalid files.

pub(crate) mod lp;
pub(crate) mod lp_tok;
pub(crate) mod mps;

pub use lp::parse_lp;
pub use mps::parse_mps;
