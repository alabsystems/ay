// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by executor::check_sat_assuming to preserve item paths.

#[cfg(test)]
mod nested_recheck_authority_tests {
    use super::super::theories::solve_harness::ProofProblemAssertionProvenance;
    use super::*;

    fn provenance_of(roots: &[TermId], window: &[TermId]) -> ProofProblemAssertionProvenance {
        ProofProblemAssertionProvenance::passthrough(roots, window)
    }

    /// The assumption-core recheck runs on the SAME executor and reaches the
    /// public publication funnel, whose unknown path calls
    /// `invalidate_last_check_result` and CLEARS the authored proof
    /// provenance. Re-rooting must reinstate the outer authority, or a later
    /// preprocessing lane rebuilds provenance from its own transformed working
    /// set and mandatory UNSAT certification rejects a correct refutation with
    /// `AssertionEpochMismatch`.
    #[test]
    fn cleared_provenance_is_restored_to_the_outer_authored_roots() {
        let mut exec = Executor::new();
        let a = exec.ctx.terms.mk_var("a", Sort::Bool);
        let b = exec.ctx.terms.mk_var("b", Sort::Bool);
        let authored = vec![a, b];
        let outer = provenance_of(&authored, &authored);

        exec.proof_problem_assertion_provenance = None;
        exec.reroot_proof_authority(Some(&outer));

        assert_eq!(exec.proof_original_problem_assertions(), authored);
    }

    /// Re-rooting NARROWS: a nested lane's transformed working set must never
    /// survive as authored authority, which is exactly the promotion that
    /// forged the 60-term "authored" set behind the certification rejection.
    #[test]
    fn nested_working_set_cannot_keep_its_own_authority() {
        let mut exec = Executor::new();
        let a = exec.ctx.terms.mk_var("a", Sort::Bool);
        let b = exec.ctx.terms.mk_var("b", Sort::Bool);
        let generated = exec.ctx.terms.mk_var("solver_generated", Sort::Bool);
        let authored = vec![a, b];
        let outer = provenance_of(&authored, &authored);

        // What a preprocessing lane installs after the clear: it treats its own
        // window (authored MINUS a folded premise, PLUS a generated axiom) as
        // the authored roots.
        let nested_window = vec![b, generated];
        exec.proof_problem_assertion_provenance =
            Some(provenance_of(&nested_window, &nested_window));

        exec.reroot_proof_authority(Some(&outer));

        let rooted = exec
            .proof_problem_assertion_provenance
            .as_ref()
            .expect("re-rooting installs provenance");
        assert_eq!(rooted.original_problem_assertions, authored);
        assert!(
            !rooted.problem_assertions.contains(&generated),
            "a solver-generated term must not become an authored premise"
        );
    }

    /// With no outer authority to rebase onto there is nothing to restore, and
    /// inventing one would be the widening this gate exists to prevent.
    #[test]
    fn absent_outer_authority_is_left_alone() {
        let mut exec = Executor::new();
        exec.proof_problem_assertion_provenance = None;
        exec.reroot_proof_authority(None);
        assert!(exec.proof_problem_assertion_provenance.is_none());
    }
}
