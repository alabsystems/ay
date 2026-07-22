// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lemma generalization utilities for PDR solver.
//!
//! This module contains functions for generalizing blocking formulas (cubes)
//! to stronger lemmas that exclude more bad states.
//!
//! ## Key concepts
//!
//! - **Generalization**: Weakening a blocking formula while maintaining inductiveness
//! - **IUC shrinking**: Using UNSAT cores to remove unnecessary conjuncts
//! - **Relational equality**: Replacing `x = k, y = j` with `x = y + c`
//! - **Binary search thresholding**: Finding optimal bound thresholds
//!
//! ## Functions
//!
//! - [`collect_conjuncts`]: Extract conjuncts from a formula (flatten nested ANDs)
//! - [`build_conjunction`]: Build a conjunction from a list of formulas
//! - [`and_all`]: Build a conjunction from an iterator of formulas
//! - [`extract_disequalities`]: Extract disequalities from an expression
//! - [`extract_equality`]: Extract a (var, value) pair from an equality conjunct
//! - [`extract_equality_or_not_distinct`]: Extract equality from `(= v c)` or `(not (distinct v c))`
//!
//! See the development design notes for full design.

mod relational;
mod utils;

// Re-export public functions
pub(super) use utils::{
    build_conjunction, collect_or_branches, extract_disequalities, extract_equality,
    extract_equality_or_not_distinct,
};
