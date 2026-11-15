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
    use crate::verification::{
        verify_conflict_semantic_memoized, ConflictSemanticVerdict, VerificationError,
    };
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
        // A fresh LIA re-solve re-derived UNSAT: the memo records that, not a
        // bare acceptance.
        assert_eq!(
            exec.conflict_semantic_verify_memo
                .values()
                .copied()
                .collect::<Vec<_>>(),
            vec![ConflictSemanticVerdict::Reproved]
        );
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
        assert_eq!(
            exec.conflict_semantic_verify_memo
                .values()
                .copied()
                .collect::<Vec<_>>(),
            vec![ConflictSemanticVerdict::Rejected]
        );
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

    /// The memo records what an ACCEPTED verification established, so a
    /// certification lane can tell a re-derivation from a pass (2026-09-23
    /// hunt: the checked-sat-refutation lane read a bare `true` as authority).
    ///
    /// * a nonlinear conflict is outside the LIA/LRA verifiers and passes the
    ///   fail-closed gate unchecked;
    /// * an array read-over-write conflict is re-derived by a combiner that
    ///   carries the array theory — the same inference that produces array
    ///   conflicts in the search, so it is recorded as such.
    #[test]
    fn memo_distinguishes_unchecked_and_array_theory_acceptances() {
        let mut exec = Executor::new();
        let x = exec.ctx.terms.mk_var("x", Sort::Int);
        let y = exec.ctx.terms.mk_var("y", Sort::Int);
        let one = exec.ctx.terms.mk_int(BigInt::from(1));
        let zero = exec.ctx.terms.mk_int(BigInt::from(0));
        let xy = exec.ctx.terms.mk_mul(vec![x, y]);
        let xy_eq_1 = exec.ctx.terms.mk_eq(xy, one);
        let x_eq_0 = exec.ctx.terms.mk_eq(x, zero);
        // {x*y = 1, x = 0}: UNSAT, but only a nonlinear procedure can say so.
        let nonlinear = vec![TheoryLit::new(xy_eq_1, true), TheoryLit::new(x_eq_0, true)];
        assert!(verify_conflict_semantic_memoized(
            &mut exec.conflict_semantic_verify_memo,
            &nonlinear,
            &exec.ctx.terms,
            &exec.active_support_axioms,
        )
        .is_ok());
        let mut key = nonlinear.clone();
        key.sort_unstable();
        assert_eq!(
            exec.conflict_semantic_verify_memo.get(&key),
            Some(&ConflictSemanticVerdict::AcceptedUnchecked)
        );

        let arr = Sort::array(Sort::Int, Sort::Int);
        let a = exec.ctx.terms.mk_var("a", arr.clone());
        let b = exec.ctx.terms.mk_var("b", arr);
        let i = exec.ctx.terms.mk_var("i", Sort::Int);
        let v = exec.ctx.terms.mk_var("v", Sort::Int);
        let stored = exec.ctx.terms.mk_store(a, i, v);
        let b_is_store = exec.ctx.terms.mk_eq(b, stored);
        let read = exec.ctx.terms.mk_select(b, i);
        let read_is_v = exec.ctx.terms.mk_eq(read, v);
        // {b = store(a, i, v), select(b, i) != v}: read-over-write refutes it.
        let row = vec![
            TheoryLit::new(b_is_store, true),
            TheoryLit::new(read_is_v, false),
        ];
        assert!(verify_conflict_semantic_memoized(
            &mut exec.conflict_semantic_verify_memo,
            &row,
            &exec.ctx.terms,
            &exec.active_support_axioms,
        )
        .is_ok());
        let mut key = row.clone();
        key.sort_unstable();
        assert_eq!(
            exec.conflict_semantic_verify_memo.get(&key),
            Some(&ConflictSemanticVerdict::ReprovedByArrayTheory)
        );
    }
}
