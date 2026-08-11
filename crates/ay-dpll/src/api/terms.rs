// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Term construction for AY Solver API.
//!
//! Variable and function declarations, function application, datatypes, arrays,
//! constants, booleans, quantifiers, comparisons, arithmetic, and conversions.

mod arithmetic;
mod arrays;
mod boolean;
mod comparisons;
mod compat;
mod constants;
mod conversions;
mod datatypes;
mod function_application;
mod function_declarations;
mod function_definitions;
mod quantifiers;
mod variables;

#[allow(deprecated)]
pub use compat::AstKind;

// The established child modules import this shared construction vocabulary
// through `use super::*`.
use ay_core::kani_compat::DetHashSet as HashSet;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;

use ay_core::term::{Symbol, TermData};
use ay_core::{DatatypeSort, Sort, TermId, TermStore};
use ay_frontend::Command;

use super::types::{NativeReplayEventKind, SolverError, SortExt, Term};
use super::Solver;
