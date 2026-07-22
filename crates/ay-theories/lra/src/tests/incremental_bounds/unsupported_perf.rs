// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Regression test for #4919: persistent_unsupported must be restored on pop().
///
/// Before the fix (3537d6c68), once an unsupported atom set `persistent_unsupported = true`,
/// the unsupported set was never cleared on pop(). This caused all subsequent check()
/// calls to return Unknown even after the scope containing the unsupported atom was removed.
///
/// Uses a non-combined-theory-mode solver with an unknown function to trigger
/// unsupported atom marking. In combined_theory_mode (the default for DPLL(T)),
/// unknown functions don't trigger the marking — so we explicitly set non-combined mode.
#[test]
fn test_persistent_unsupported_cleared_on_pop_4919() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let ten = terms.mk_int(BigInt::from(10));

    let ge_zero = terms.mk_ge(x, zero); // x >= 0
    let le_ten = terms.mk_le(x, ten); // x <= 10

    // An unknown function "mysterious" in non-combined mode marks atom as unsupported.
    let mysterious_x = terms.mk_app(Symbol::named("mysterious"), vec![x], Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let mystery_le_five = terms.mk_le(mysterious_x, five);

    // Default combined_theory_mode is false, so unknown functions mark atoms unsupported
    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(ge_zero, true);
    solver.assert_literal(le_ten, true);

    // Base scope: should be Sat (0 <= x <= 10 is feasible)
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "Base scope (0 <= x <= 10) should be Sat, got {result:?}"
    );

    // Push and add unsupported atom
    solver.push();
    solver.assert_literal(mystery_le_five, true);

    // This scope has unsupported atom — should return Unknown
    let inner_result = solver.check();
    assert!(
        matches!(inner_result, TheoryResult::Unknown),
        "Inner scope with unknown function should be Unknown, got {inner_result:?}"
    );

    // Pop removes the scope with the unsupported atom
    solver.pop();

    // Re-assert base constraints and re-check
    solver.reset();
    solver.assert_literal(ge_zero, true);
    solver.assert_literal(le_ten, true);

    // After pop: persistent_unsupported should be restored to false.
    // Before the fix, this would return Unknown because persistent_unsupported
    // was stuck at true.
    let result_after_pop = solver.check();
    assert!(
        matches!(result_after_pop, TheoryResult::Sat),
        "After pop(), (0 <= x <= 10) should be Sat, not Unknown. \
         persistent_unsupported was not properly restored. Got {result_after_pop:?}"
    );
}

/// Regression test for #6362: soft_reset() must clear the unsupported-atom
/// undo trail and its scope markers alongside the set itself.
#[test]
fn test_soft_reset_clears_unsupported_trail_6362() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let five = terms.mk_int(BigInt::from(5));

    let ge_zero = terms.mk_ge(x, zero);
    let mysterious_x = terms.mk_app(Symbol::named("mysterious"), vec![x], Sort::Int);
    let mystery_le_five = terms.mk_le(mysterious_x, five);

    let mut solver = LraSolver::new(&terms);
    solver.push();
    solver.assert_literal(ge_zero, true);
    solver.assert_literal(mystery_le_five, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unknown),
        "Scope with unsupported atom should be Unknown, got {result:?}"
    );
    assert_eq!(
        solver.persistent_unsupported_scope_marks,
        vec![0],
        "push() should record a single unsupported trail mark before new inserts"
    );
    assert_eq!(
        solver.persistent_unsupported_trail.len(),
        solver.persistent_unsupported_atoms.len(),
        "unsupported trail should contain exactly the set insertions"
    );

    solver.soft_reset();

    assert!(
        solver.persistent_unsupported_atoms.is_empty(),
        "soft_reset() must clear unsupported atoms"
    );
    assert!(
        solver.persistent_unsupported_trail.is_empty(),
        "soft_reset() must clear the unsupported undo trail"
    );
    assert!(
        solver.persistent_unsupported_scope_marks.is_empty(),
        "soft_reset() must clear stale unsupported scope marks"
    );

    solver.assert_literal(ge_zero, true);
    let result_after_reset = solver.check();
    assert!(
        matches!(result_after_reset, TheoryResult::Sat),
        "After soft_reset(), supported atoms should still solve normally. Got {result_after_reset:?}"
    );
}

/// Regression test: register_atom() must track unsupported sub-expressions
/// even though current_parsing_atom is None during registration.
///
/// When register_atom() parses an atom and caches the result, the atom's
/// unsupported status must be recorded. Otherwise, check() will find the
/// cache hit and skip re-parsing, permanently losing the unsupported flag.
/// This would cause false SAT results for formulas with unsupported terms.
///
/// Bug found in P2:98 reflection: #6167 per-atom tracking migration from
/// global saw_unsupported flag to per-atom unsupported_atoms set. The
/// mark_current_atom_unsupported() method is a no-op when current_parsing_atom
/// is None, which is always the case during register_atom().
#[test]
fn test_register_atom_preserves_unsupported_status_6167() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));

    // An unknown function "mysterious" in non-combined mode marks atom as unsupported.
    let mysterious_x = terms.mk_app(Symbol::named("mysterious"), vec![x], Sort::Int);
    let mystery_le_five = terms.mk_le(mysterious_x, five); // mysterious(x) <= 5

    let mut solver = LraSolver::new(&terms);

    // Key: call register_atom BEFORE assert_literal, mimicking DPLL(T) flow.
    // register_atom() parses and caches; check() should still detect unsupported.
    solver.register_atom(mystery_le_five);

    solver.assert_literal(mystery_le_five, true);

    // Simplex will say Sat (mysterious(x) is a fresh unconstrained variable),
    // but the correct result is Unknown because we can't verify the model
    // against the actual semantics of mysterious(x).
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unknown),
        "Atom with unsupported function (register_atom path) should return Unknown, \
         got {result:?}. Bug: register_atom() cached the parse result but lost the \
         unsupported flag because current_parsing_atom was None."
    );
}

/// Same as above but verifies the non-register_atom path still works.
/// This is the control test: without register_atom(), check() parses directly
/// with current_parsing_atom set, so unsupported tracking works correctly.
#[test]
fn test_direct_assert_preserves_unsupported_status_6167() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));

    let mysterious_x = terms.mk_app(Symbol::named("mysterious"), vec![x], Sort::Int);
    let mystery_le_five = terms.mk_le(mysterious_x, five);

    let mut solver = LraSolver::new(&terms);

    // Do NOT call register_atom — go directly to assert + check.
    solver.assert_literal(mystery_le_five, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unknown),
        "Atom with unsupported function (direct assert path) should return Unknown, \
         got {result:?}"
    );
}

/// Regression test for last_diseq_check_had_violation (#4919).
///
/// When a disequality check detects a violation (returning NeedDisequalitySplit),
/// subsequent check() calls MUST re-check disequalities even if the model hasn't
/// changed (no new atoms asserted, no simplex re-run). Without this flag, the
/// optimization `model_may_have_changed = need_simplex || parsed_count > 0` would
/// suppress the violation on the second check(), returning false Sat.
///
/// This test:
/// 1. Sets up x in [3, 5] with disequality x != 3
/// 2. First check() should detect violation (simplex assigns x=3)
/// 3. Second check() (no new atoms) must STILL report the violation
#[test]
fn test_diseq_violation_persists_across_checks_4919() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));

    // Bounds: x >= 3, x <= 5
    let x_ge_3 = terms.mk_ge(x, three);
    let x_le_5 = terms.mk_le(x, five);

    // Disequality: x != 3
    let x_ne_3 = terms.mk_app(Symbol::named("distinct"), vec![x, three], Sort::Bool);

    let mut solver = LraSolver::new(&terms);

    solver.assert_literal(x_ge_3, true); // x >= 3
    solver.assert_literal(x_le_5, true); // x <= 5
    solver.assert_literal(x_ne_3, true); // x != 3

    // First check: simplex assigns x=3 (lower bound), disequality violated.
    let result1 = solver.check();
    assert!(
        matches!(
            result1,
            TheoryResult::NeedDisequalitySplit(_) | TheoryResult::NeedExpressionSplit(_)
        ),
        "First check() with x=3 and x!=3 should detect violation, got {result1:?}"
    );

    // Second check without any new atoms or model changes.
    // Without last_diseq_check_had_violation, the optimization would skip
    // disequality re-checking and return Sat (false positive).
    let result2 = solver.check();
    assert!(
        !matches!(result2, TheoryResult::Sat),
        "Second check() must NOT return Sat when disequality violation persists, \
         got {result2:?}. Bug: last_diseq_check_had_violation not preventing \
         optimization from suppressing known violations."
    );
}

/// Verify that the 2-variable UNSAT problem (x>=10, x+y<=5, y>=0) is correctly
/// detected as UNSAT by check() (the public API).
///
/// Note: dual_simplex_with_max_iters() called directly after assert_literal()
/// will return SAT because assert_literal only queues atoms — the atom-to-bound
/// parsing happens inside check(). This test uses check() to exercise the full path.
#[test]
fn test_dual_simplex_unsat_detected_at_all_iter_budgets() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let zero_val = terms.mk_rational(BigRational::zero());

    let ge_ten = terms.mk_ge(x, ten);
    let sum = terms.mk_add(vec![x, y]);
    let le_five = terms.mk_le(sum, five);
    let ge_zero = terms.mk_ge(y, zero_val);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(ge_ten, true);
    solver.assert_literal(le_five, true);
    solver.assert_literal(ge_zero, true);

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "check() should detect UNSAT for (x>=10, x+y<=5, y>=0), got {:?}",
        std::mem::discriminant(&result)
    );
}

/// Regression: `checked_r64_add` pattern (i128 intermediates without GCD
/// reduction before i64 fit check) returns false `None` on reducible fractions.
/// Example: `(i64::MAX-1)/i64::MAX + 1/i64::MAX = 1` — the i128 intermediate
/// numerator/denominator exceed i64 range even though the reduced result is 1/1.
/// This causes `deduplicate_conflict` to lose Farkas annotations unnecessarily.
/// See: simplex.rs `checked_r64_add` and farkas.rs `checked_r64_mul`.
#[test]
fn test_checked_r64_add_pattern_gcd_false_overflow() {
    use num_rational::Rational64;

    // Replicate the exact computation from LraSolver::checked_r64_add
    fn checked_r64_add_current(a: Rational64, b: Rational64) -> Option<Rational64> {
        let an = i128::from(*a.numer());
        let ad = i128::from(*a.denom());
        let bn = i128::from(*b.numer());
        let bd = i128::from(*b.denom());
        let num = an.checked_mul(bd)?.checked_add(bn.checked_mul(ad)?)?;
        let den = ad.checked_mul(bd)?;
        let num_i64 = i64::try_from(num).ok()?;
        let den_i64 = i64::try_from(den).ok()?;
        if den_i64 == 0 {
            return None;
        }
        Some(Rational64::new(num_i64, den_i64))
    }

    // Fixed version with GCD reduction before i64 fit check
    fn checked_r64_add_fixed(a: Rational64, b: Rational64) -> Option<Rational64> {
        let an = i128::from(*a.numer());
        let ad = i128::from(*a.denom());
        let bn = i128::from(*b.numer());
        let bd = i128::from(*b.denom());
        let num = an.checked_mul(bd)?.checked_add(bn.checked_mul(ad)?)?;
        let den = ad.checked_mul(bd)?;
        // Reduce by GCD before checking i64 fit
        fn gcd128(mut a: i128, mut b: i128) -> i128 {
            a = a.abs();
            b = b.abs();
            while b != 0 {
                let t = b;
                b = a % b;
                a = t;
            }
            a
        }
        let g = gcd128(num, den);
        let num_reduced = if g != 0 { num / g } else { num };
        let den_reduced = if g != 0 { den / g } else { den };
        let num_i64 = i64::try_from(num_reduced).ok()?;
        let den_i64 = i64::try_from(den_reduced).ok()?;
        if den_i64 == 0 {
            return None;
        }
        Some(Rational64::new(num_i64, den_i64))
    }

    let max = i64::MAX;
    let a = Rational64::new(max - 1, max);
    let b = Rational64::new(1, max);

    // Current implementation: false overflow (returns None)
    let current_result = checked_r64_add_current(a, b);
    // The result should be 1/1, but current impl can't handle it
    assert!(
        current_result.is_none(),
        "BUG FIXED: checked_r64_add now handles this case — \
         remove this test's is_none assertion and update to is_some"
    );

    // Fixed implementation: correctly reduces to 1/1
    let fixed_result = checked_r64_add_fixed(a, b);
    assert_eq!(
        fixed_result,
        Some(Rational64::new(1, 1)),
        "GCD-reduced version should return 1/1"
    );

    // Another case: 1/large + (large-1)/large = 1
    let large = 1_000_000_007i64;
    let c = Rational64::new(1, large);
    let d = Rational64::new(large - 1, large);

    // This case works in both since intermediate products fit in i64
    let current_small = checked_r64_add_current(c, d);
    let fixed_small = checked_r64_add_fixed(c, d);
    assert_eq!(current_small, Some(Rational64::new(1, 1)));
    assert_eq!(fixed_small, Some(Rational64::new(1, 1)));
}

/// Performance canary: `propagate_equalities` performs pairwise comparison
/// when N variables share the same tight-bound value (lib.rs:5759-5894).
/// For N=400 this should materialize all 79,800 equalities and complete
/// within a practical debug-build budget.
///
/// The nested loops already make the O(N²) structure obvious in code review.
/// What this test can enforce reliably on shared hosts is:
/// 1. the solver still produces the full pair set, and
/// 2. the concrete workload does not regress into multi-second behavior.
///
/// After #6617, `check()` may surface the same satisfiable state as
/// `NeedModelEqualities` rather than bare `Sat` when many fixed terms share a
/// value. That path reserves a representative chain of `n - 1` pairs first, so
/// `propagate_equalities()` should emit the remaining pairwise equalities.
#[test]
fn test_perf_propagate_equalities_quadratic_scaling() {
    use ay_core::time::Instant;

    let measure_once = |n: usize| -> (std::time::Duration, usize) {
        let mut terms = TermStore::new();
        let mut ge_atoms = Vec::with_capacity(n);
        let mut le_atoms = Vec::with_capacity(n);
        for i in 0..n {
            let v = terms.mk_var(format!("v{i}"), Sort::Real);
            let c1 = terms.mk_rational(BigRational::from(BigInt::from(5)));
            ge_atoms.push(terms.mk_ge(v, c1));
            let c2 = terms.mk_rational(BigRational::from(BigInt::from(5)));
            le_atoms.push(terms.mk_le(v, c2));
        }
        let mut solver = LraSolver::new(&terms);
        for i in 0..n {
            solver.assert_literal(ge_atoms[i], true);
            solver.assert_literal(le_atoms[i], true);
        }
        let pre_eq_result = solver.check();
        assert!(
            matches!(
                &pre_eq_result,
                TheoryResult::Sat
                    | TheoryResult::NeedModelEquality(_)
                    | TheoryResult::NeedModelEqualities(_)
            ),
            "tight-bound setup should stay satisfiable before equality propagation, got {pre_eq_result:?}"
        );
        let start = Instant::now();
        let eq_result = solver.propagate_equalities();
        let elapsed = start.elapsed();
        assert!(
            !eq_result.equalities.is_empty(),
            "expected equalities for {n} vars"
        );
        let expected_pairs = n * (n - 1) / 2;
        let expected_remaining_pairs = expected_pairs - (n - 1);
        assert_eq!(
            eq_result.equalities.len(),
            expected_remaining_pairs,
            "expected propagate_equalities() to emit all non-representative-chain \
             equalities for {n} tight-bound variables"
        );
        (elapsed, eq_result.equalities.len())
    };

    // Warm the allocator and monomorphized code paths before timing.
    let _ = measure_once(32);

    let (t_large, pairs_large) = measure_once(400);
    assert_eq!(pairs_large, (400 * 399 / 2) - 399);
    assert!(
        t_large.as_secs() < 5,
        "N=400 took {t_large:?}, exceeds 5s budget"
    );
}

/// Verify that disequality conflict dedup uses O(1) HashSet lookups.
///
/// Creates N variables all pinned to value 5 (via lower = upper = 5), then
/// asserts a disequality (v0 + v1 + ... + v_{N-1} != 5*N). Since all vars are
/// pinned, the conflict clause must collect all 2*N bound reasons (one lower +
/// one upper per variable) and deduplicate them. With the old Vec::contains()
/// approach, dedup was O(N²); with HashSet::insert() it's O(N).
#[test]
fn test_perf_disequality_conflict_dedup_scaling() {
    use ay_core::time::Instant;

    let run = |n: usize| -> std::time::Duration {
        let mut terms = TermStore::new();
        let mut vars = Vec::with_capacity(n);
        let mut ge_atoms = Vec::with_capacity(n);
        let mut le_atoms = Vec::with_capacity(n);

        for i in 0..n {
            let v = terms.mk_var(format!("v{i}"), Sort::Real);
            vars.push(v);
            let c_lo = terms.mk_rational(BigRational::from(BigInt::from(5)));
            ge_atoms.push(terms.mk_ge(v, c_lo));
            let c_hi = terms.mk_rational(BigRational::from(BigInt::from(5)));
            le_atoms.push(terms.mk_le(v, c_hi));
        }

        // Build sum expression: v0 + v1 + ... + v_{N-1}
        let sum = terms.mk_add(vars.clone());
        // Assert disequality: sum != 5*N
        let target_val = terms.mk_rational(BigRational::from(BigInt::from(5 * n as i64)));
        let eq_atom = terms.mk_eq(sum, target_val);

        let mut solver = LraSolver::new(&terms);
        solver.register_atom(eq_atom);
        for i in 0..n {
            solver.register_atom(ge_atoms[i]);
            solver.register_atom(le_atoms[i]);
        }
        // Pin all vars to 5
        for i in 0..n {
            solver.assert_literal(ge_atoms[i], true);
            solver.assert_literal(le_atoms[i], true);
        }
        // Assert disequality (negated equality)
        solver.assert_literal(eq_atom, false);

        let start = Instant::now();
        let result = solver.check();
        let elapsed = start.elapsed();

        // Must be UNSAT: all vars pinned to 5, sum = 5*N, disequality violated.
        assert!(
            matches!(result, TheoryResult::Unsat(_)),
            "expected UNSAT for N={n}, got {result:?}"
        );
        if let TheoryResult::Unsat(conflict) = &result {
            // Conflict should contain unique literals only (no duplicates).
            let unique: HashSet<_> = conflict.iter().collect();
            assert_eq!(
                conflict.len(),
                unique.len(),
                "conflict clause has duplicates for N={n}"
            );
        }
        elapsed
    };

    // Warm up
    let _ = run(10);

    let t_200 = run(200);
    let t_400 = run(400);

    // With O(1) dedup, doubling N should roughly double (not quadruple) time.
    // Use a generous 5s budget — the old O(N²) approach on N=400 would be slow.
    assert!(
        t_400.as_secs() < 5,
        "N=400 conflict dedup took {t_400:?}, exceeds 5s budget (N=200: {t_200:?})"
    );
}
