// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

mod equality_propagation;
mod shared_constraints;

impl LraSolver {
    pub(crate) fn propagate_equalities_inner(&mut self) -> EqualityPropagationResult {
        self.propagate_equalities_impl()
    }

    pub(crate) fn assert_shared_equality_inner(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        reason: &[TheoryLit],
    ) {
        self.assert_shared_equality_impl(lhs, rhs, reason);
    }

    pub(crate) fn assert_shared_disequality_inner(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        reason: &[TheoryLit],
    ) {
        self.assert_shared_disequality_impl(lhs, rhs, reason);
    }
}
