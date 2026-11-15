// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The ground oracle the search asks, and the store it builds terms in.
//!
//! The engine owns no `Executor`: every satisfiability question goes through
//! [`QlraHost::check`]. Answers are HINTS. A wrong `Sat` model can only yield
//! a useless instance, a wrong `Unsat` can only propose a refutation or a
//! saturation that the publication routes re-derive independently (strict
//! consequence replay for UNSAT, the quantified model gate for SAT).

use ay_core::{TermId, TermStore};
use num_rational::BigRational;

/// One requested value from a satisfying assignment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum OracleValue {
    Rat(BigRational),
    Bool(bool),
}

/// The oracle's answer to one quantifier-free query.
#[derive(Clone, Debug)]
pub(crate) enum OracleAnswer {
    Unsat,
    /// Values for the requested targets, positionally; `None` when the model
    /// did not determine a value.
    Sat(Vec<Option<OracleValue>>),
    Unknown,
}

/// Term store plus ground oracle plus stop control.
pub(crate) trait QlraHost {
    /// The store every engine term is minted in.
    fn terms(&mut self) -> &mut TermStore;
    /// Decide the conjunction of `assertions` (quantifier-free) and, on SAT,
    /// report the values of `targets`.
    fn check(&mut self, assertions: &[TermId], targets: &[TermId]) -> OracleAnswer;
    /// Interrupt / deadline poll.
    fn should_stop(&self) -> bool;
}
