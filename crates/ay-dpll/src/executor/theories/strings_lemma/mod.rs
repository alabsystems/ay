// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! String theory lemma clause creation and length axiom collection.
//!
//! Translates symbolic `StringLemma` requests into concrete CNF clauses,
//! and collects string-length axioms from term roots.

mod clauses;
mod guards;
mod len_axioms;

#[cfg(test)]
pub(in crate::executor) use guards::{build_reason_guard, emit_guard_empty_splits};

#[cfg(test)]
mod tests;
