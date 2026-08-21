// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by executor::check_sat to preserve item paths.

#[cfg(test)]
mod conflict_semantic_memo_tests {
    //! Unit tests for the per-check-sat conflict-verification verdict memo
    //! (#4535 memoized verifier) wired through the Executor field: both
    //! verdict polarities are cached keyed by the sorted literal set, and
    //! cached verdicts agree with direct verification.

    use super::super::Executor;
    use crate::verification::{verify_conflict_semantic_memoized, VerificationError};
    use ay_core::{Sort, TheoryLit};
    use num_bigint::BigInt;

    /// A genuinely-UNSAT conflict verifies Ok, is memoized as Ok, and an
    /// identical conflict (in any literal order) hits the memo with Ok.
    #[test]
    fn memoizes_ok_verdict_and_hits_on_reordered_identical_conflict() {
        let mut exec = Executor::new();
        let x = exec.ctx.terms.mk_var("x", Sort::Int);
        let zero = exec.ctx.terms.mk_int(BigInt::from(0));
        let x_eq_0 = exec.ctx.terms.mk_eq(x, zero);
        let x_le_0 = exec.ctx.terms.mk_le(x, zero);
        let zero_le_x = exec.ctx.terms.mk_le(zero, x);
        // {x != 0, x <= 0, 0 <= x} — jointly UNSAT (the #6853 shape).
        let conflict = vec![
            TheoryLit::new(x_eq_0, false),
            TheoryLit::new(x_le_0, true),
            TheoryLit::new(zero_le_x, true),
        ];
        assert!(verify_conflict_semantic_memoized(
            &mut exec.conflict_semantic_verify_memo,
            &conflict,
            &exec.ctx.terms,
            &exec.active_support_axioms,
        )
        .is_ok());
        assert_eq!(exec.conflict_semantic_verify_memo.len(), 1);
        // Reordered identical set: memo hit, same verdict, no new entry.
        let reordered = vec![conflict[2], conflict[0], conflict[1]];
        assert!(verify_conflict_semantic_memoized(
            &mut exec.conflict_semantic_verify_memo,
            &reordered,
            &exec.ctx.terms,
            &exec.active_support_axioms,
        )
        .is_ok());
        assert_eq!(exec.conflict_semantic_verify_memo.len(), 1);
    }

    /// A spurious (satisfiable) conflict fails verification, is memoized as
    /// Err, and the memoized re-check STAYS Err (fail-closed is preserved
    /// across the cache — a cached failure can never admit a clause).
    #[test]
    fn memoizes_err_verdict_and_stays_fail_closed() {
        let mut exec = Executor::new();
        let x = exec.ctx.terms.mk_var("x", Sort::Int);
        let zero = exec.ctx.terms.mk_int(BigInt::from(0));
        let ten = exec.ctx.terms.mk_int(BigInt::from(10));
        let x_ge_0 = exec.ctx.terms.mk_ge(x, zero);
        let x_le_10 = exec.ctx.terms.mk_le(x, ten);
        // {x >= 0, x <= 10} — satisfiable, so verification must reject.
        let conflict = vec![TheoryLit::new(x_ge_0, true), TheoryLit::new(x_le_10, true)];
        assert!(matches!(
            verify_conflict_semantic_memoized(
                &mut exec.conflict_semantic_verify_memo,
                &conflict,
                &exec.ctx.terms,
                &exec.active_support_axioms,
            ),
            Err(VerificationError::ConflictIsSat)
        ));
        assert_eq!(exec.conflict_semantic_verify_memo.len(), 1);
        // Memo hit: still an error (Internal carries the memo attribution).
        assert!(matches!(
            verify_conflict_semantic_memoized(
                &mut exec.conflict_semantic_verify_memo,
                &conflict,
                &exec.ctx.terms,
                &exec.active_support_axioms,
            ),
            Err(VerificationError::Internal(_))
        ));
        assert_eq!(exec.conflict_semantic_verify_memo.len(), 1);
    }
}
