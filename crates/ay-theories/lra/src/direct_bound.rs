// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact direct-bound API for private theory clients.

use super::*;

impl LraSolver {
    /// Assert an exact linear bound `sum(coeffs) {>=,>,<=,<} bound` over
    /// already-interned terms, for callers that build a linear system directly
    /// rather than from SMT atoms.
    ///
    /// This is [`LraSolver::add_gomory_cut`]'s strict-capable sibling. NRA's
    /// model-guided grounding uses it for Motzkin/template systems containing
    /// strict disjuncts, where replacing `>` with `>=` or guessing an epsilon
    /// would be incorrect.
    ///
    /// `reason` must be a real non-sentinel term. Invalid direct requests are
    /// ignored rather than manufacturing an unjustified bound.
    pub fn assert_linear_bound(
        &mut self,
        coefficients: &[(u32, BigRational)],
        bound: &BigRational,
        is_lower: bool,
        strict: bool,
        reason: TermId,
    ) {
        if coefficients.is_empty() || reason.is_sentinel() {
            return;
        }
        let expression = LinearExpr {
            coeffs: coefficients
                .iter()
                .map(|(variable, coefficient)| (*variable, Rational::from_big(coefficient.clone())))
                .collect(),
            constant: Rational::zero(),
        };
        let bound_type = if is_lower {
            BoundType::Lower
        } else {
            BoundType::Upper
        };
        self.assert_bound(
            expression,
            Rational::from_big(bound.clone()),
            bound_type,
            strict,
            reason,
            true,
        );
        self.dirty = true;
    }
}
