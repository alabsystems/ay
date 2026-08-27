// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact-authored-`false` refutation: the canonical replacement proof for a
//! problem whose own text asserts the Boolean constant.

use super::*;

impl Executor {
    /// Replace an arbitrary UNSAT derivation with the canonical proof from an
    /// exact authored `false` premise.
    ///
    /// This is deliberately an identity test against the strict checker's
    /// authored problem scope.  A normalized term that happens to fold to
    /// `false`, a solver-injected `false`, or any non-Boolean lookalike cannot
    /// authorize the rewrite.  The candidate is checked atomically before it
    /// replaces the original proof, so a checker/printer rule mismatch fails
    /// closed and leaves the original (possibly trust-bearing) proof visible.
    pub(super) fn replace_with_exact_authored_false_refutation(&mut self, proof: &mut Proof) {
        let false_term = self.ctx.terms.false_term();
        // A canonical `false` TermId is not enough: elaboration also maps any
        // authored contradiction (for example `x - x <= -1`) to that same
        // identifier. The shared premise-authority gate admits only exact
        // literal-false assertion or assumption provenance.
        if !self.boolean_constant_premises_authored().1
            || !matches!(
                self.ctx.terms.get(false_term),
                TermData::Const(Constant::Bool(false))
            )
        {
            return;
        }

        // Alethe's `false` rule proves `(not false)`.  Resolve that tautology
        // against the exact authored `false` assumption to obtain the empty
        // clause.  No trust/hole/theory shortcut participates.
        let not_false = self.ctx.terms.mk_not_raw(false_term);
        let mut candidate = Proof::new();
        let premise = candidate.add_assume(false_term, Some("exact_authored_false".to_string()));
        let tautology =
            candidate.add_rule_step(AletheRule::False, vec![not_false], Vec::new(), Vec::new());
        candidate.add_resolution(Vec::new(), false_term, premise, tautology);

        if self.check_proof_strict_with_datatypes(&candidate).is_ok() {
            *proof = candidate;
        }
    }
}
