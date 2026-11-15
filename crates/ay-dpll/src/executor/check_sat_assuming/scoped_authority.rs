// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact proof authority while a scoped solve merges its assumption roots.

use ay_core::TermId;

use super::super::theories::solve_harness::ProofProblemAssertionProvenance;
use super::Executor;

impl Executor {
    /// Add only the supplied assumption roots to an existing authored scope.
    /// The combined assertion window can contain generated axioms and must
    /// never be used as an identity provenance for this purpose.
    pub(super) fn install_scoped_assumption_authority(
        &mut self,
        assumptions: &[TermId],
    ) -> Option<ProofProblemAssertionProvenance> {
        let saved = self.proof_problem_assertion_provenance.clone()?;
        let mut scoped = saved.clone();
        for &assumption in assumptions {
            if !scoped.original_problem_assertions.contains(&assumption) {
                scoped.original_problem_assertions.push(assumption);
            }
            if !scoped.problem_assertions.contains(&assumption) {
                scoped.problem_assertions.push(assumption);
            }
            let sources = scoped.assertion_sources.entry(assumption).or_default();
            if !sources
                .iter()
                .any(|source| source.as_slice() == [assumption])
            {
                sources.push(vec![assumption]);
            }
        }
        self.proof_problem_assertion_provenance = Some(scoped);
        Some(saved)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::executor_types::{Result, SolveResult};
    use ay_core::Sort;

    fn panicking_solve(executor: &mut Executor) -> Result<SolveResult> {
        assert!(executor.last_assumptions.is_none());
        let generated = executor.ctx.terms.mk_var("generated", Sort::Bool);
        executor.proof_problem_assertion_provenance = Some(
            ProofProblemAssertionProvenance::passthrough(&[generated], &[generated]),
        );
        panic!("simulated scoped solve panic");
    }

    #[test]
    fn scoped_panic_restores_assertions_assumptions_and_exact_authority() {
        for with_authority in [false, true] {
            let mut executor = Executor::new();
            let base = executor.ctx.terms.mk_var("base", Sort::Bool);
            let assumption = executor.ctx.terms.mk_var("assumption", Sort::Bool);
            executor.ctx.assertions = vec![base];
            executor.last_assumptions = Some(vec![assumption]);
            if with_authority {
                executor.proof_problem_assertion_provenance = Some(
                    ProofProblemAssertionProvenance::passthrough(&[base], &[base]),
                );
            }
            let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                executor.solve_scoped_assumptions(&[base], &[assumption], panicking_solve)
            }));
            assert!(outcome.is_err());
            assert_eq!(executor.ctx.assertions, [base]);
            assert_eq!(executor.last_assumptions, Some(vec![assumption]));
            let restored = executor.proof_problem_assertion_provenance.as_ref();
            if with_authority {
                let restored = restored.expect("saved authority restored");
                assert_eq!(restored.original_problem_assertions, [base]);
                assert_eq!(restored.problem_assertions, [base]);
                assert_eq!(restored.assertion_sources.len(), 1);
                assert_eq!(restored.assertion_sources[&base], [vec![base]]);
            } else {
                assert!(restored.is_none());
            }
        }
    }

    #[test]
    fn scoped_authority_adds_exact_assumptions_and_restores_epoch_roots() {
        let mut executor = Executor::new();
        let base = executor.ctx.terms.mk_var("base", Sort::Bool);
        let assumption = executor.ctx.terms.mk_var("assumption", Sort::Bool);
        let generated = executor.ctx.terms.mk_var("generated", Sort::Bool);
        let outer = ProofProblemAssertionProvenance::passthrough(&[base], &[base, generated]);
        executor.proof_problem_assertion_provenance = Some(outer.clone());
        let saved = executor.install_scoped_assumption_authority(&[assumption, assumption]);
        let scoped = executor
            .proof_problem_assertion_provenance
            .as_ref()
            .unwrap();
        assert_eq!(scoped.original_problem_assertions, [base, assumption]);
        assert_eq!(scoped.problem_assertions, [base, assumption]);
        assert_eq!(scoped.assertion_sources[&assumption], [vec![assumption]]);
        assert!(!scoped.assertion_sources.contains_key(&generated));
        executor.reroot_proof_authority(saved.as_ref());
        let restored = executor
            .proof_problem_assertion_provenance
            .as_ref()
            .unwrap();
        assert_eq!(
            restored.original_problem_assertions,
            outer.original_problem_assertions
        );
        assert_eq!(restored.problem_assertions, outer.problem_assertions);
        assert!(!restored.assertion_sources.contains_key(&assumption));
    }

    #[test]
    fn scoped_subset_authority_never_borrows_other_public_assumptions() {
        let mut executor = Executor::new();
        let base = executor.ctx.terms.mk_var("base", Sort::Bool);
        let first = executor.ctx.terms.mk_var("first", Sort::Bool);
        let omitted = executor.ctx.terms.mk_var("omitted", Sort::Bool);
        executor.proof_problem_assertion_provenance = Some(
            ProofProblemAssertionProvenance::passthrough(&[base], &[base]),
        );
        executor.last_assumptions = Some(vec![first, omitted]);
        let saved = executor.install_scoped_assumption_authority(&[first]);
        let scoped = executor
            .proof_problem_assertion_provenance
            .as_ref()
            .unwrap();
        assert_eq!(scoped.original_problem_assertions, [base, first]);
        assert!(!scoped.assertion_sources.contains_key(&omitted));
        executor.reroot_proof_authority(saved.as_ref());
    }
}
