// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Restore the public assertion window around NIA arithmetic preprocessing.

use std::panic::{catch_unwind, resume_unwind, AssertUnwindSafe};

use crate::executor::theories::solve_harness::ProofProblemAssertionProvenance;
use crate::executor_types::{Result, SolveResult};
use crate::preprocess::VariableSubstitution;
use crate::Executor;

impl Executor {
    pub(super) fn preprocess_nia_theory_window(&mut self) -> (VariableSubstitution, bool) {
        let mut symbolic_sources = None;
        // Symbolic mod/div elimination for the NIA path (#nia-modxx-zerodiv).
        //
        // `preprocess_lia_artifacts` only eliminates `(mod a k)` / `(div a k)`
        // with a CONSTANT divisor `k`. A `(mod a b)` with a non-constant divisor
        // (e.g. `(mod x x)`) is left intact, and the LRA layer then flags every
        // atom containing it as UNSUPPORTED and silently DROPS it from the
        // tableau. NIA's tentative-patch path treats LRA's "Sat with unsupported
        // atoms" as feasible and returns SAT on a model that violates those
        // dropped atoms (e.g. `(<= (* y y) (mod x x))` with `y*y=1, (mod x x)=-1`)
        // — a wrong-SAT.
        //
        // Eliminating symbolic mod/div here replaces `(mod x x)` with a single
        // fresh integer `r` constrained by the SMT-LIB division axioms
        // (`x = x*q + r ∧ 0 ≤ r < |x|`, or unconstrained when `x = 0`). Both
        // occurrences resolve to the SAME `r` because the term store hash-conses
        // `(mod x x)` and the elimination is run ONCE over the whole assertion
        // list (shared memo) — so the zero-divisor result stays a single
        // consistent value across all its uses (the congruence the constant-path
        // already enforces). The atoms then become ordinary (non)linear LIA
        // constraints that the tableau actually enforces.
        //
        // SOUNDNESS: the symbolic axiom over-approximates nothing — it is the
        // exact SMT-LIB semantics of `mod`/`div`, with the zero-divisor case left
        // unconstrained (matching z3). When the elimination introduces an
        // unconstrained zero-divisor var, SAT must route through the
        // `sat_validated_by_mod_div_or_branch` bypass because the model evaluator
        // cannot replay `(mod a 0)` (#div0).
        if crate::executor::mod_div_elim::contains_symbolic_int_mod_div(
            &self.ctx.terms,
            &self.ctx.assertions,
        ) {
            let assertions = std::mem::take(&mut self.ctx.assertions);
            let mod_elim = crate::executor::mod_div_elim::eliminate_int_mod_div(
                &mut self.ctx.terms,
                &assertions,
            );
            if mod_elim.introduced_unconstrained_div_mod {
                self.sat_validated_by_mod_div_or_branch = true;
            }
            let mut rewritten = mod_elim.constraints;
            rewritten.extend(mod_elim.rewritten);
            self.ctx.assertions = rewritten;
            symbolic_sources = Some(assertions);
        }

        let artifacts = self.preprocess_lia_artifacts();
        let original_assertions = std::mem::replace(&mut self.ctx.assertions, artifacts.assertions);
        let original_problem_assertions = symbolic_sources.unwrap_or(original_assertions);
        let proof_provenance = ProofProblemAssertionProvenance::from_sources(
            original_problem_assertions,
            &self.ctx.assertions,
            artifacts.assertion_sources.clone(),
        )
        .preserving_authority_from(self.proof_problem_assertion_provenance.as_ref());
        self.set_counterexample_style(crate::CounterexampleStyle::Any);
        self.proof_problem_assertion_provenance = Some(proof_provenance);
        (
            artifacts.var_subst,
            artifacts.introduced_unconstrained_div_mod,
        )
    }

    pub(super) fn with_nia_theory_window<T, F>(&mut self, solve: F) -> Result<(SolveResult, T)>
    where
        F: FnOnce(&mut Self) -> Result<(SolveResult, T)>,
    {
        // This replaces solve_nia's existing source-root copy. The inner
        // producer moves the actual input vector into its proof provenance.
        let assertions = self.ctx.assertions.clone();
        let style = self.counterexample_style();
        let provenance = self.proof_problem_assertion_provenance.clone();
        let div_mod_validation = self.sat_validated_by_mod_div_or_branch;
        let outcome = catch_unwind(AssertUnwindSafe(|| solve(self)));

        self.ctx.assertions = assertions;
        self.set_counterexample_style(style);
        // Retain a refuting window's licensed source bridge for certification,
        // using the same policy as the other arithmetic theory windows.
        let restore_provenance = match &outcome {
            Ok(Ok((result, _))) => {
                !result.is_unsat() || !self.theory_window_provenance_survives_unsat()
            }
            Ok(Err(_)) | Err(_) => true,
        };
        if restore_provenance {
            self.proof_problem_assertion_provenance = provenance;
        }
        if !matches!(&outcome, Ok(Ok(_))) {
            self.sat_validated_by_mod_div_or_branch = div_mod_validation;
        }

        match outcome {
            Ok(result) => result,
            Err(payload) => resume_unwind(payload),
        }
    }
}

#[cfg(test)]
mod tests;
