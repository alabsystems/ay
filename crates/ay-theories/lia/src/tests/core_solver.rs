// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn add_pairwise_disequalities(
    terms: &mut TermStore,
    atoms: &mut Vec<(TermId, bool)>,
    vars: &[TermId],
) {
    for i in 0..vars.len() {
        for j in (i + 1)..vars.len() {
            let eq = terms.mk_eq(vars[i], vars[j]);
            atoms.push((eq, false));
        }
    }
}

#[test]
fn test_lia_solver_trivial_sat() {
    let terms = TermStore::new();
    let mut solver = LiaSolver::new(&terms);

    // Empty problem is SAT
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn test_lia_needs_final_check_after_sat_for_bcp() {
    let terms = TermStore::new();
    assert!(LiaSolver::new(&terms).needs_final_check_after_sat());
}

#[test]
fn test_lia_solver_timeout_callback_returns_unknown() {
    let terms = TermStore::new();
    let mut solver = LiaSolver::new(&terms);
    solver.set_timeout_callback(|| true);
    assert!(matches!(solver.check(), TheoryResult::Unknown));
}

#[test]
fn test_lia_solver_integer_bound() {
    let mut terms = TermStore::new();

    // x <= 5 where x is an integer
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let atom = terms.mk_le(x, five);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(atom, true);

    // Should be SAT (x can be any integer <= 5)
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn test_lia_solver_conflicting_bounds() {
    let mut terms = TermStore::new();

    // x >= 10 and x <= 5 should be UNSAT
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let ten = terms.mk_int(BigInt::from(10));

    let le_atom = terms.mk_le(x, five); // x <= 5
    let ge_atom = terms.mk_ge(x, ten); // x >= 10

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(le_atom, true);
    solver.assert_literal(ge_atom, true);

    let result = solver.check();
    assert!(matches!(
        result,
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
    ));
}

#[test]
fn test_lia_check_during_propagate_keeps_gcd_unsat() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let two_x = terms.mk_mul(vec![two, x]);
    let eq = terms.mk_eq(two_x, one);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);

    let result = solver.check_during_propagate();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "BCP-time LIA check must keep local GCD conflicts, got {result:?}"
    );
}

#[test]
fn test_lia_check_during_propagate_defers_disequality_conflict() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));

    let neq_five = terms.mk_eq(x, five);
    let ge_five = terms.mk_ge(x, five);
    let le_five = terms.mk_le(x, five);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(neq_five, false);
    solver.assert_literal(ge_five, true);
    solver.assert_literal(le_five, true);

    assert!(
        matches!(solver.check_during_propagate(), TheoryResult::Sat),
        "BCP-time LIA check should defer disequality/model-only work to the final check"
    );

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_)
                | TheoryResult::UnsatWithFarkas(_)
                | TheoryResult::NeedDisequalitySplit(_)
                | TheoryResult::NeedExpressionSplit(_)
        ),
        "final LIA check must still revisit the deferred disequality, got {result:?}"
    );
}

#[test]
fn test_lia_check_during_propagate_preserves_final_dioph_rerun() {
    // Contract: after BCP-time + full checks, the equality system must be
    // solved (Dioph caches populated) — cascade-UNSAT benchmarks rely on
    // Dioph running at BCP time too (#8733). Whether the caches end up
    // populated by the BCP-time run or the final `check()` is an
    // implementation detail.
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let eq = terms.mk_eq(x, y);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);

    assert!(
        matches!(solver.check_during_propagate(), TheoryResult::Sat),
        "BCP-time LIA check should return Sat when no local conflict exists"
    );

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "full LIA check should still solve the deferred equality system, got {result:?}"
    );
    assert!(
        !solver.dioph_cached_substitutions.is_empty(),
        "Dioph solving must run (at BCP time or final check) for equality-dense problems"
    );
}

#[test]
fn test_lia_affine_substitution_chain_unsat_issue_51() {
    let mut terms = TermStore::new();

    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));

    let b_plus_one = terms.mk_add(vec![b, one]);
    let c_minus_one = terms.mk_sub(vec![c, one]);
    let eq_a = terms.mk_eq(a, b_plus_one);
    let eq_b = terms.mk_eq(b, c_minus_one);
    let eq_ac = terms.mk_eq(a, c);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq_a, true);
    solver.assert_literal(eq_b, true);
    solver.assert_literal(eq_ac, false);

    let result = solver.check();
    assert_conflict_soundness(result, LiaSolver::new(&terms));
}

#[test]
fn test_lia_affine_substitution_chain_sat_offset_issue_51() {
    let mut terms = TermStore::new();

    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));

    let b_plus_one = terms.mk_add(vec![b, one]);
    let c_minus_two = terms.mk_sub(vec![c, two]);
    let eq_a = terms.mk_eq(a, b_plus_one);
    let eq_b = terms.mk_eq(b, c_minus_two);
    let eq_ac = terms.mk_eq(a, c);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq_a, true);
    solver.assert_literal(eq_b, true);
    solver.assert_literal(eq_ac, false);

    let result = solver.check();
    assert!(
        !matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "a=c-1 with a!=c is satisfiable; got {result:?}"
    );
}

#[test]
fn test_modular_unsat_conflict_includes_bound_reasons() {
    let mut terms = TermStore::new();

    // r = 2*x, r = 1 is infeasible over integers (r must be even).
    // The modular UNSAT explanation must include both the equality and
    // the bound literals that force r = 1.
    let x = terms.mk_var("x", Sort::Int);
    let r = terms.mk_var("r", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));

    let two_x = terms.mk_mul(vec![two, x]);
    let eq = terms.mk_eq(r, two_x);
    let r_ge_1 = terms.mk_ge(r, one);
    let r_le_1 = terms.mk_le(r, one);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(r_ge_1, true);
    solver.assert_literal(r_le_1, true);

    let result = solver.check();
    let TheoryResult::Unsat(conflict) = result else {
        panic!("Expected modular UNSAT with explicit conflict literals, got {result:?}");
    };

    assert!(
        conflict.iter().any(|lit| lit.term == eq && lit.value),
        "Conflict must include equality literal"
    );
    assert!(
        conflict.iter().any(|lit| lit.term == r_ge_1 && lit.value),
        "Conflict must include lower-bound literal"
    );
    assert!(
        conflict.iter().any(|lit| lit.term == r_le_1 && lit.value),
        "Conflict must include upper-bound literal"
    );
}

#[test]
fn test_lia_solver_integer_infeasible() {
    let mut terms = TermStore::new();

    // x > 5 and x < 6 where x is integer - UNSAT (no integer between 5 and 6)
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let six = terms.mk_int(BigInt::from(6));

    let gt_atom = terms.mk_gt(x, five); // x > 5
    let lt_atom = terms.mk_lt(x, six); // x < 6

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(gt_atom, true);
    solver.assert_literal(lt_atom, true);

    // LRA would say SAT with x = 5.5, but LIA should reject
    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "{result:?}"
    );
}

#[test]
fn test_lia_solver_integer_feasible() {
    let mut terms = TermStore::new();

    // x >= 5 and x <= 6 where x is integer - SAT (x can be 5 or 6)
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let six = terms.mk_int(BigInt::from(6));

    let ge_atom = terms.mk_ge(x, five); // x >= 5
    let le_atom = terms.mk_le(x, six); // x <= 6

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(ge_atom, true);
    solver.assert_literal(le_atom, true);

    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat));
}

#[test]
fn test_lia_solver_linear_constraint() {
    let mut terms = TermStore::new();

    // 2*x >= 5 where x is integer
    // LRA: x >= 2.5, so x = 2.5 is valid
    // LIA: x must be integer, so x >= 3
    let x = terms.mk_var("x", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let five = terms.mk_int(BigInt::from(5));

    let scaled = terms.mk_mul(vec![two, x]);
    let ge_atom = terms.mk_ge(scaled, five); // 2*x >= 5

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(ge_atom, true);

    // LRA gives x = 2.5 which is non-integer, so LIA returns NeedSplit
    // to request a splitting lemma (x <= 2) OR (x >= 3)
    // This is the correct branch-and-bound behavior - the DPLL layer
    // should handle the split and eventually find x = 3.
    let result = solver.check();
    assert!(matches!(
        result,
        TheoryResult::Sat | TheoryResult::NeedSplit(_)
    ));
}

#[test]
fn test_parse_linear_expr_with_negated_constant_mul() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let neg_one = terms.mk_neg(one); // Represents `(- 1)`
    let neg_x = terms.mk_mul(vec![neg_one, x]); // Represents `(* (- 1) x)`

    let solver = LiaSolver::new(&terms);
    let (coeffs, constant) = solver.parse_linear_expr_with_vars(neg_x, zero);

    assert_eq!(constant, BigInt::from(0));
    assert_eq!(coeffs.len(), 1);
    assert_eq!(coeffs.get(&x), Some(&BigInt::from(-1)));
}

#[test]
fn test_lia_solver_push_pop() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let five = terms.mk_int(BigInt::from(5));

    let ge_atom = terms.mk_ge(x, three); // x >= 3
    let le_atom = terms.mk_le(x, five); // x <= 5

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(ge_atom, true);

    assert!(matches!(solver.check(), TheoryResult::Sat));

    // Push and add constraint
    solver.push();
    solver.assert_literal(le_atom, true);

    assert!(matches!(solver.check(), TheoryResult::Sat));

    // Pop should restore previous state
    solver.pop();
    // After pop, only ge_atom is asserted
    solver.reset();
    solver.assert_literal(ge_atom, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn test_reset_clears_dioph_substitution_cache() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let eq = terms.mk_eq(x, y);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    let _ = solver.check();

    assert!(
        !solver.dioph_cached_substitutions.is_empty(),
        "Dioph cache should be populated after solving x = y"
    );
    assert!(
        !solver.dioph_cached_reasons.is_empty(),
        "Dioph reasons should track equality literals"
    );

    solver.reset();

    assert!(solver.dioph_equality_key.is_empty());
    assert!(solver.dioph_safe_dependent_vars.is_empty());
    assert!(solver.dioph_cached_substitutions.is_empty());
    assert!(solver.dioph_cached_reasons.is_empty());
}

/// Regression test: pop() must not let STALE Dioph caches be reused (#3736).
///
/// Under #C8 the equality-derived Dioph caches are PRESERVED across pop (they
/// depend only on the asserted equality SET, not on the inequality bounds that
/// backtracking churns) and re-validated by the `dioph_equality_key` comparison
/// on the next check(). When the asserted equality set changed — here it becomes
/// empty after the pop removes `x = y` — the stale caches are dropped before any
/// reuse, preserving the #3736 soundness guarantee without re-solving Dioph
/// after every backtrack.
#[test]
fn test_pop_revalidates_dioph_caches() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let eq = terms.mk_eq(x, y);

    let mut solver = LiaSolver::new(&terms);

    solver.push();
    solver.assert_literal(eq, true);
    let _ = solver.check();

    assert!(
        !solver.dioph_cached_substitutions.is_empty(),
        "Dioph cache should be populated after solving x = y in scope"
    );

    solver.pop();

    // #C8: caches are preserved across pop but flagged for re-validation; the
    // equality_key comparison on the next check() is the staleness gate.
    assert!(
        solver.dioph_needs_revalidation,
        "pop must flag the dioph caches for re-validation"
    );

    // The next check() re-validates against the now-empty equality set and
    // drops the stale caches before they can be reused (#3736 soundness).
    let _ = solver.check();
    assert!(
        solver.dioph_equality_key.is_empty(),
        "dioph_equality_key must be empty after re-validation with no equalities"
    );
    assert!(
        solver.dioph_cached_substitutions.is_empty(),
        "stale dioph_cached_substitutions must be dropped on re-validation"
    );
    assert!(
        solver.dioph_cached_reasons.is_empty(),
        "stale dioph_cached_reasons must be dropped on re-validation"
    );
}

/// #C8: when the asserted equality set is UNCHANGED across a pop (the popped
/// scope only added/removed inequality bounds), the equality-derived Dioph
/// caches are preserved and reused — no redundant re-solve. This is the
/// per-backtrack cost reduction the fix targets.
#[test]
fn test_pop_preserves_dioph_caches_when_equalities_unchanged() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let eq = terms.mk_eq(x, y);
    let ten = terms.mk_int(BigInt::from(10));
    let bound = terms.mk_le(x, ten);

    let mut solver = LiaSolver::new(&terms);

    // Equality asserted at the OUTER scope so it survives the inner pop.
    solver.assert_literal(eq, true);
    let _ = solver.check();
    let key_before = solver.dioph_equality_key.clone();
    let subs_before = solver.dioph_cached_substitutions.len();
    assert!(
        subs_before > 0,
        "Dioph cache should be populated after solving x = y"
    );

    // Inner scope tightens an inequality only; the equality set is unchanged.
    solver.push();
    solver.assert_literal(bound, true);
    let _ = solver.check();
    solver.pop();

    let _ = solver.check();
    assert_eq!(
        solver.dioph_equality_key, key_before,
        "equality key must be unchanged across a bound-only push/pop"
    );
    assert_eq!(
        solver.dioph_cached_substitutions.len(),
        subs_before,
        "dioph substitutions must be preserved (not re-solved from scratch) \
         when the equality set is unchanged across pop"
    );
}

/// Regression test: pop() must restore cut-local state (#3685).
#[test]
fn test_pop_restores_cut_state() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);

    let mut solver = LiaSolver::new(&terms);
    solver.learned_cuts.push(StoredCut {
        coeffs: vec![(x, BigRational::from(BigInt::from(1)))],
        bound: BigRational::from(BigInt::from(0)),
        is_lower: true,
        reasons: Vec::new(),
    });
    solver.record_seen_hnf_cut(HnfCutKey {
        coeffs: vec![(x, BigInt::from(1))],
        bound: BigInt::from(0),
    });

    solver.push();
    solver.learned_cuts.push(StoredCut {
        coeffs: vec![(x, BigRational::from(BigInt::from(2)))],
        bound: BigRational::from(BigInt::from(1)),
        is_lower: false,
        reasons: Vec::new(),
    });
    solver.record_seen_hnf_cut(HnfCutKey {
        coeffs: vec![(x, BigInt::from(2))],
        bound: BigInt::from(1),
    });
    solver.gomory_iterations = 3;
    solver.hnf_iterations = 5;

    solver.pop();

    assert_eq!(
        solver.learned_cuts.len(),
        1,
        "pop must truncate learned cuts"
    );
    assert_eq!(
        solver.learned_cuts[0].bound,
        BigRational::from(BigInt::from(0)),
        "pre-scope learned cut should remain after pop"
    );
    // Outer scope had gomory_iterations=0 and hnf_iterations=0 at push time.
    // pop() must restore those values, not leave inner scope's 3 and 5.
    assert_eq!(
        solver.gomory_iterations, 0,
        "gomory iteration counter must be restored to outer scope value on pop"
    );
    assert_eq!(
        solver.hnf_iterations, 0,
        "hnf iteration counter must be restored to outer scope value on pop"
    );
    // Outer scope had 1 entry in seen_hnf_cuts at push time.
    // pop() must restore it, not clear to empty or leave inner scope's 2 entries.
    assert_eq!(
        solver.seen_hnf_cuts.len(),
        1,
        "seen_hnf_cuts must be restored to outer scope value on pop"
    );
    assert!(
        solver.seen_hnf_cuts.contains(&HnfCutKey {
            coeffs: vec![(x, BigInt::from(1))],
            bound: BigInt::from(0),
        }),
        "outer scope's seen HNF cut must be present after pop"
    );
}

/// Regression test: pop() restores non-zero outer cut state (#3685).
///
/// Verifies that when the outer scope has non-zero gomory/hnf iterations,
/// pop() restores those values rather than resetting to 0.
#[test]
fn test_pop_restores_nonzero_outer_cut_state() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);

    let mut solver = LiaSolver::new(&terms);

    // Simulate outer scope having done some cut work
    solver.gomory_iterations = 2;
    solver.hnf_iterations = 4;
    solver.record_seen_hnf_cut(HnfCutKey {
        coeffs: vec![(x, BigInt::from(1))],
        bound: BigInt::from(0),
    });
    solver.record_seen_hnf_cut(HnfCutKey {
        coeffs: vec![(x, BigInt::from(3))],
        bound: BigInt::from(7),
    });

    solver.push();

    // Inner scope does more cut work
    solver.gomory_iterations = 6;
    solver.hnf_iterations = 10;
    solver.record_seen_hnf_cut(HnfCutKey {
        coeffs: vec![(x, BigInt::from(5))],
        bound: BigInt::from(99),
    });

    solver.pop();

    // Must restore outer scope's values, not reset to 0
    assert_eq!(
        solver.gomory_iterations, 2,
        "gomory_iterations must be restored to outer scope value (2), not reset to 0"
    );
    assert_eq!(
        solver.hnf_iterations, 4,
        "hnf_iterations must be restored to outer scope value (4), not reset to 0"
    );
    assert_eq!(
        solver.seen_hnf_cuts.len(),
        2,
        "seen_hnf_cuts must be restored to outer scope's 2 entries, not inner scope's 3 or empty"
    );
}

#[test]
fn test_dioph_cache_clears_when_no_equalities_remain() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));

    let eq = terms.mk_eq(x, y);
    let y_ge_0 = terms.mk_ge(y, zero);
    let y_le_0 = terms.mk_le(y, zero);
    let x_ge_1 = terms.mk_ge(x, one);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    let _ = solver.check();

    assert!(
        !solver.dioph_cached_substitutions.is_empty(),
        "Expected cached substitution from x = y"
    );

    // clear_assertions intentionally preserves Dioph caches. A subsequent
    // no-equality check must invalidate them.
    solver.clear_assertions();
    solver.assert_literal(y_ge_0, true);
    solver.assert_literal(y_le_0, true);
    solver.assert_literal(x_ge_1, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "Inequality-only system should stay SAT after cache invalidation, got {result:?}"
    );

    assert!(solver.dioph_equality_key.is_empty());
    assert!(solver.dioph_safe_dependent_vars.is_empty());
    assert!(solver.dioph_cached_substitutions.is_empty());
    assert!(solver.dioph_cached_reasons.is_empty());
}

#[test]
fn test_is_integer() {
    assert!(LiaSolver::is_integer(&BigRational::from(BigInt::from(5))));
    assert!(LiaSolver::is_integer(&BigRational::from(BigInt::from(0))));
    assert!(LiaSolver::is_integer(&BigRational::from(BigInt::from(-10))));

    // 5/2 = 2.5 is not an integer
    let half = BigRational::new(BigInt::from(5), BigInt::from(2));
    assert!(!LiaSolver::is_integer(&half));

    // 6/3 = 2 is an integer (should simplify)
    let two = BigRational::new(BigInt::from(6), BigInt::from(3));
    assert!(LiaSolver::is_integer(&two));
}

#[test]
fn test_split_request_floor_ceil_negative() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let _solver = LiaSolver::new(&terms);

    let s = LiaSolver::create_split_request(x, BigRational::new(BigInt::from(-1), BigInt::from(2)));
    assert_eq!(s.floor, BigInt::from(-1));
    assert_eq!(s.ceil, BigInt::from(0));

    let s = LiaSolver::create_split_request(x, BigRational::new(BigInt::from(-3), BigInt::from(2)));
    assert_eq!(s.floor, BigInt::from(-2));
    assert_eq!(s.ceil, BigInt::from(-1));

    let s = LiaSolver::create_split_request(x, BigRational::new(BigInt::from(7), BigInt::from(2)));
    assert_eq!(s.floor, BigInt::from(3));
    assert_eq!(s.ceil, BigInt::from(4));
}

#[test]
fn test_hnf_density_threshold_is_half_or_more_equalities() {
    assert!(!LiaSolver::is_equality_dense(0, 0));
    assert!(!LiaSolver::is_equality_dense(0, 4));
    assert!(!LiaSolver::is_equality_dense(1, 4));
    assert!(LiaSolver::is_equality_dense(2, 4));
    assert!(LiaSolver::is_equality_dense(3, 5));
    assert_eq!(LiaSolver::hnf_iteration_budget(1, 4), 2);
    assert_eq!(LiaSolver::hnf_iteration_budget(2, 4), 20);
}

#[test]
fn test_branch_selection_prefers_smallest_boxed_span() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);

    // x is fixed to 1/2 (boxed with span 0).
    let two = terms.mk_int(BigInt::from(2));
    let one = terms.mk_int(BigInt::from(1));
    let two_x = terms.mk_mul(vec![two, x]);
    let x_eq_half = terms.mk_eq(two_x, one);

    // y is boxed but with a much wider feasible range:
    // 10*y >= 11 (y >= 1.1 in the relaxation), y <= 100.
    let ten = terms.mk_int(BigInt::from(10));
    let eleven = terms.mk_int(BigInt::from(11));
    let hundred = terms.mk_int(BigInt::from(100));
    let ten_y = terms.mk_mul(vec![ten, y]);
    let y_ge = terms.mk_ge(ten_y, eleven);
    let y_le = terms.mk_le(y, hundred);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(x_eq_half, true);
    solver.assert_literal(y_ge, true);
    solver.assert_literal(y_le, true);

    assert!(matches!(solver.lra.check(), TheoryResult::Sat));

    let (split_var, _) = solver
        .check_integer_constraints()
        .expect("expected at least one fractional integer variable");
    assert_eq!(
        split_var, x,
        "branching must prioritize smallest boxed span first"
    );

    let x_span = solver.bound_span(x).expect("x should be boxed");
    let y_span = solver.bound_span(y).expect("y should be boxed");
    assert!(x_span < y_span, "test setup requires x_span < y_span");
}

#[test]
fn test_lia_model_extraction() {
    let mut terms = TermStore::new();

    // x = 5 where x is integer
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let eq_atom = terms.mk_eq(x, five);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq_atom, true);

    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat));

    // Extract and verify model
    if let Some(model) = solver.extract_model() {
        if let Some(val) = model.values.get(&x) {
            assert_eq!(*val, BigInt::from(5));
        }
    }
}

#[test]
fn test_lia_solver_two_var_equality_not_immediately_unsat() {
    let mut terms = TermStore::new();

    // 4*x + 3*y = 70, x >= 0, y >= 0, x <= 41 is satisfiable over integers.
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let four = terms.mk_int(BigInt::from(4));
    let three = terms.mk_int(BigInt::from(3));
    let seventy = terms.mk_int(BigInt::from(70));
    let zero = terms.mk_int(BigInt::from(0));
    let forty_one = terms.mk_int(BigInt::from(41));

    let four_x = terms.mk_mul(vec![four, x]);
    let three_y = terms.mk_mul(vec![three, y]);
    let lhs = terms.mk_add(vec![four_x, three_y]);
    let eq = terms.mk_eq(lhs, seventy);
    let x_ge = terms.mk_ge(x, zero);
    let y_ge = terms.mk_ge(y, zero);
    let x_le = terms.mk_le(x, forty_one);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(x_ge, true);
    solver.assert_literal(y_ge, true);
    solver.assert_literal(x_le, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat | TheoryResult::NeedSplit(_)),
        "{result:?}"
    );
}

#[test]
fn test_gcd_test_unsat() {
    let mut terms = TermStore::new();

    // 4*x + 4*y + 4*z - 2*w = 49
    // GCD(4, 4, 4, 2) = 2, but 2 does not divide 49, so UNSAT
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);

    let four = terms.mk_int(BigInt::from(4));
    let minus_two = terms.mk_int(BigInt::from(-2));
    let forty_nine = terms.mk_int(BigInt::from(49));

    let four_x = terms.mk_mul(vec![four, x]);
    let four_y = terms.mk_mul(vec![four, y]);
    let four_z = terms.mk_mul(vec![four, z]);
    let minus_two_w = terms.mk_mul(vec![minus_two, w]);

    let lhs = terms.mk_add(vec![four_x, four_y, four_z, minus_two_w]);
    let eq = terms.mk_eq(lhs, forty_nine);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "GCD test should detect UNSAT: {result:?}"
    );
}

#[test]
fn test_gcd_test_sat() {
    let mut terms = TermStore::new();

    // 2*x + 4*y = 10
    // GCD(2, 4) = 2, and 2 divides 10, so may be SAT
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);

    let two = terms.mk_int(BigInt::from(2));
    let four = terms.mk_int(BigInt::from(4));
    let ten = terms.mk_int(BigInt::from(10));

    let two_x = terms.mk_mul(vec![two, x]);
    let four_y = terms.mk_mul(vec![four, y]);

    let lhs = terms.mk_add(vec![two_x, four_y]);
    let eq = terms.mk_eq(lhs, ten);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);

    let result = solver.check();
    // GCD test should NOT reject this (2 divides 10)
    // It may be SAT or NeedSplit (for branch-and-bound)
    assert!(
        !matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "GCD test should not reject valid equation: {result:?}"
    );
}

/// Test basic GCD divisibility check.
///
/// This test verifies that the basic GCD test correctly detects UNSAT
/// when the GCD of coefficients does not divide the constant term.
/// Note: This exercises basic GCD, not ext_gcd_test interval arithmetic.
#[test]
fn test_gcd_divisibility_unsat() {
    let mut terms = TermStore::new();

    // Setup: 2*x + 6*y = -1 where -2 <= x <= 2
    //
    // Basic GCD test: GCD(2, 6) = 2, and 2 does NOT divide -1.
    // Therefore this should be UNSAT.
    //
    // The bounds on x don't matter here because the basic GCD test
    // detects the infeasibility before ext_gcd_test is reached.

    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);

    let two = terms.mk_int(BigInt::from(2));
    let six = terms.mk_int(BigInt::from(6));
    let neg_one = terms.mk_int(BigInt::from(-1));
    let neg_two = terms.mk_int(BigInt::from(-2));
    let pos_two = terms.mk_int(BigInt::from(2));

    let two_x = terms.mk_mul(vec![two, x]);
    let six_y = terms.mk_mul(vec![six, y]);

    // 2*x + 6*y = -1
    let lhs = terms.mk_add(vec![two_x, six_y]);
    let eq = terms.mk_eq(lhs, neg_one);

    // Bounds on x: -2 <= x <= 2
    let x_ge_neg2 = terms.mk_le(neg_two, x);
    let x_le_pos2 = terms.mk_le(x, pos_two);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(x_ge_neg2, true);
    solver.assert_literal(x_le_pos2, true);

    let result = solver.check();

    // Basic GCD test: GCD(2,6)=2 doesn't divide -1, so UNSAT
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "GCD(2,6)=2 doesn't divide -1, so UNSAT expected: {result:?}"
    );
}

/// Test extended GCD with negative-spanning interval that is SAT.
///
/// Creates a scenario where l_rat < 0 < u_rat but a solution exists.
#[test]
fn test_ext_gcd_negative_spanning_sat() {
    let mut terms = TermStore::new();

    // Setup: 1*x + 4*y = 2 where -3 <= x <= 1
    //
    // GCD(1, 4) = 1, which divides 2, so basic GCD test passes.
    // For ext_gcd_test:
    // - x has coeff 1 (smallest), bounded [-3, 1]
    // - y has coeff 4, unbounded
    // - gcds = 4
    // - l_rat = 2 + 1*(-3) = -1, u_rat = 2 + 1*(1) = 3
    // - l1 = ceil(-1/4) = ceil(-0.25) = 0
    // - u1 = floor(3/4) = floor(0.75) = 0
    // - Since u1 >= l1 (0 >= 0), there may be a solution.
    //
    // Concrete check: x=2, y=0 => 2 + 0 = 2 ✓ (but x=2 outside bounds)
    // x=-2, y=1 => -2 + 4 = 2 ✓ (x=-2 is in bounds!)
    // So there IS a solution.

    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);

    let one = terms.mk_int(BigInt::from(1));
    let four = terms.mk_int(BigInt::from(4));
    let two_const = terms.mk_int(BigInt::from(2));
    let neg_three = terms.mk_int(BigInt::from(-3));
    let pos_one = terms.mk_int(BigInt::from(1));

    let one_x = terms.mk_mul(vec![one, x]);
    let four_y = terms.mk_mul(vec![four, y]);

    // 1*x + 4*y = 2
    let lhs = terms.mk_add(vec![one_x, four_y]);
    let eq = terms.mk_eq(lhs, two_const);

    // Bounds on x: -3 <= x <= 1
    let x_ge_neg3 = terms.mk_le(neg_three, x);
    let x_le_pos1 = terms.mk_le(x, pos_one);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(x_ge_neg3, true);
    solver.assert_literal(x_le_pos1, true);

    let result = solver.check();

    // This should NOT be UNSAT - solution exists: x=-2, y=1
    // Verification: 1*(-2) + 4*1 = -2 + 4 = 2 ✓
    assert!(
        !matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "Solution x=-2, y=1 exists (1*-2 + 4*1 = 2), should not be UNSAT: {result:?}"
    );
}

#[test]
fn test_lia_direct_enumeration_two_free_vars_fixes_solution() {
    let mut terms = TermStore::new();

    // Create vars in order so equalities pivot on (c, d) and leave (a, b) as free vars.
    let c = terms.mk_var("c", Sort::Int);
    let d = terms.mk_var("d", Sort::Int);
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);

    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let minus_one = terms.mk_int(BigInt::from(-1));

    // c = a + b
    let a_plus_b = terms.mk_add(vec![a, b]);
    let eq_c = terms.mk_eq(c, a_plus_b);

    // d = a - b
    let neg_b = terms.mk_mul(vec![minus_one, b]);
    let a_minus_b = terms.mk_add(vec![a, neg_b]);
    let eq_d = terms.mk_eq(d, a_minus_b);

    // 0 <= a <= 1, 0 <= b <= 1
    let a_ge_0 = terms.mk_ge(a, zero);
    let a_le_1 = terms.mk_le(a, one);
    let b_ge_0 = terms.mk_ge(b, zero);
    let b_le_1 = terms.mk_le(b, one);

    // Regression guard: direct enumeration should return a SAT witness model for a uniquely
    // determined integer solution, without clamping bounds (which can break incremental ALL-SAT).
    let eq_c_2 = terms.mk_eq(c, two);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq_c, true);
    solver.assert_literal(eq_d, true);
    solver.assert_literal(a_ge_0, true);
    solver.assert_literal(a_le_1, true);
    solver.assert_literal(b_ge_0, true);
    solver.assert_literal(b_le_1, true);
    solver.assert_literal(eq_c_2, true);

    assert!(matches!(solver.lra.check(), TheoryResult::Sat));

    let (a_lb0, a_ub0) = solver.lra.get_bounds(a).unwrap();
    assert_ne!(a_lb0.as_ref().unwrap().value, a_ub0.as_ref().unwrap().value);

    let res = solver.try_direct_enumeration();
    let DirectEnumResult::SatWitness = res else {
        panic!("Expected SAT witness, got {res:?}");
    };
    let model = solver
        .direct_enum_witness
        .as_ref()
        .expect("Witness should be stored");
    assert_eq!(model.values.get(&a), Some(&BigInt::one()));
    assert_eq!(model.values.get(&b), Some(&BigInt::one()));

    // Bounds remain intact (0..1), not clamped to the witnessed point.
    let (a_lb1, a_ub1) = solver.lra.get_bounds(a).unwrap();
    assert_ne!(a_lb1.as_ref().unwrap().value, a_ub1.as_ref().unwrap().value);
    let (b_lb1, b_ub1) = solver.lra.get_bounds(b).unwrap();
    assert_ne!(b_lb1.as_ref().unwrap().value, b_ub1.as_ref().unwrap().value);
}

#[test]
fn test_lia_direct_enumeration_handles_bool_constants() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let one = terms.mk_int(BigInt::one());
    let eq = terms.mk_eq(x, one);

    // The term layer can fold tautologies (e.g., X = X) to a constant `true`.
    // Direct enumeration should treat these as satisfied, not as an unsupported atom.
    let t = terms.mk_bool(true);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(t, true);

    assert!(matches!(solver.lra.check(), TheoryResult::Sat));

    let res = solver.try_direct_enumeration();
    let DirectEnumResult::SatWitness = res else {
        panic!("Expected SAT witness, got {res:?}");
    };
    let model = solver
        .direct_enum_witness
        .as_ref()
        .expect("Witness should be stored");
    assert_eq!(model.values.get(&x), Some(&BigInt::one()));
}

#[test]
fn test_lia_finite_domain_search_solves_8_queens_distinct_8762() {
    let mut terms = TermStore::new();

    let queens: Vec<_> = (0..8)
        .map(|idx| terms.mk_var(format!("q{idx}"), Sort::Int))
        .collect();
    let zero = terms.mk_int(BigInt::zero());
    let seven = terms.mk_int(BigInt::from(7));

    let mut atoms = Vec::new();
    for &queen in &queens {
        atoms.push((terms.mk_ge(queen, zero), true));
        atoms.push((terms.mk_le(queen, seven), true));
    }

    for i in 0..queens.len() {
        for j in (i + 1)..queens.len() {
            let eq_rows = terms.mk_eq(queens[i], queens[j]);
            atoms.push((eq_rows, false));

            let i_term = terms.mk_int(BigInt::from(i));
            let j_term = terms.mk_int(BigInt::from(j));
            let diag_a_i = terms.mk_add(vec![queens[i], i_term]);
            let diag_a_j = terms.mk_add(vec![queens[j], j_term]);
            let eq_diag_a = terms.mk_eq(diag_a_i, diag_a_j);
            atoms.push((eq_diag_a, false));

            let i_term = terms.mk_int(BigInt::from(i));
            let j_term = terms.mk_int(BigInt::from(j));
            let diag_b_i = terms.mk_sub(vec![queens[i], i_term]);
            let diag_b_j = terms.mk_sub(vec![queens[j], j_term]);
            let eq_diag_b = terms.mk_eq(diag_b_i, diag_b_j);
            atoms.push((eq_diag_b, false));
        }
    }

    let mut solver = LiaSolver::new(&terms);
    for (atom, value) in atoms {
        solver.assert_literal(atom, value);
    }

    assert!(matches!(solver.check(), TheoryResult::Sat));
    let model = solver
        .direct_enum_witness
        .as_ref()
        .expect("finite-domain search should store the 8-queens witness");
    for (col_a, &qa) in queens.iter().enumerate() {
        for (col_b, &qb) in queens.iter().enumerate().skip(col_a + 1) {
            let row_a = model.values.get(&qa).expect("queen must have a row");
            let row_b = model.values.get(&qb).expect("queen must have a row");
            assert_ne!(row_a, row_b);
            assert_ne!(row_a + BigInt::from(col_a), row_b + BigInt::from(col_b));
            assert_ne!(row_a - BigInt::from(col_a), row_b - BigInt::from(col_b));
        }
    }
}

#[test]
fn test_lia_finite_domain_search_solves_send_more_money_8762() {
    let mut terms = TermStore::new();

    let s = terms.mk_var("S", Sort::Int);
    let e = terms.mk_var("E", Sort::Int);
    let n = terms.mk_var("N", Sort::Int);
    let d = terms.mk_var("D", Sort::Int);
    let m = terms.mk_var("M", Sort::Int);
    let o = terms.mk_var("O", Sort::Int);
    let r = terms.mk_var("R", Sort::Int);
    let y = terms.mk_var("Y", Sort::Int);
    let vars = [s, e, n, d, m, o, r, y];

    let zero = terms.mk_int(BigInt::zero());
    let one = terms.mk_int(BigInt::one());
    let nine = terms.mk_int(BigInt::from(9));
    let mut atoms = Vec::new();
    for &var in &vars {
        atoms.push((terms.mk_ge(var, zero), true));
        atoms.push((terms.mk_le(var, nine), true));
    }
    atoms.push((terms.mk_ge(s, one), true));
    atoms.push((terms.mk_ge(m, one), true));
    add_pairwise_disequalities(&mut terms, &mut atoms, &vars);

    let c10 = terms.mk_int(BigInt::from(10));
    let c100 = terms.mk_int(BigInt::from(100));
    let c1000 = terms.mk_int(BigInt::from(1000));
    let c10000 = terms.mk_int(BigInt::from(10000));
    let lhs_s = terms.mk_mul(vec![c1000, s]);
    let lhs_e = terms.mk_mul(vec![c100, e]);
    let lhs_n = terms.mk_mul(vec![c10, n]);
    let lhs_m = terms.mk_mul(vec![c1000, m]);
    let lhs_o = terms.mk_mul(vec![c100, o]);
    let lhs_r = terms.mk_mul(vec![c10, r]);
    let lhs = terms.mk_add(vec![lhs_s, lhs_e, lhs_n, d, lhs_m, lhs_o, lhs_r, e]);
    let rhs_m = terms.mk_mul(vec![c10000, m]);
    let rhs_o = terms.mk_mul(vec![c1000, o]);
    let rhs_n = terms.mk_mul(vec![c100, n]);
    let rhs_e = terms.mk_mul(vec![c10, e]);
    let rhs = terms.mk_add(vec![rhs_m, rhs_o, rhs_n, rhs_e, y]);
    let eq_sum = terms.mk_eq(lhs, rhs);
    atoms.push((eq_sum, true));

    let mut solver = LiaSolver::new(&terms);
    for (atom, value) in atoms {
        solver.assert_literal(atom, value);
    }

    assert!(matches!(solver.check(), TheoryResult::Sat));
    let model = solver
        .direct_enum_witness
        .as_ref()
        .expect("finite-domain search should store the cryptarithm witness");
    assert_eq!(model.values.get(&s), Some(&BigInt::from(9)));
    assert_eq!(model.values.get(&e), Some(&BigInt::from(5)));
    assert_eq!(model.values.get(&n), Some(&BigInt::from(6)));
    assert_eq!(model.values.get(&d), Some(&BigInt::from(7)));
    assert_eq!(model.values.get(&m), Some(&BigInt::from(1)));
    assert_eq!(model.values.get(&o), Some(&BigInt::from(0)));
    assert_eq!(model.values.get(&r), Some(&BigInt::from(8)));
    assert_eq!(model.values.get(&y), Some(&BigInt::from(2)));
}

#[test]
fn test_lia_finite_domain_search_solves_sudoku_9x9_8762() {
    let mut terms = TermStore::new();

    let cells: Vec<Vec<_>> = (0..9)
        .map(|row| {
            (0..9)
                .map(|col| terms.mk_var(format!("c{row}{col}"), Sort::Int))
                .collect()
        })
        .collect();
    let one = terms.mk_int(BigInt::one());
    let nine = terms.mk_int(BigInt::from(9));
    let mut atoms = Vec::new();

    for row in &cells {
        for &cell in row {
            atoms.push((terms.mk_ge(cell, one), true));
            atoms.push((terms.mk_le(cell, nine), true));
        }
    }

    let clues = [
        [5, 3, 0, 0, 7, 0, 0, 0, 0],
        [6, 0, 0, 1, 9, 5, 0, 0, 0],
        [0, 9, 8, 0, 0, 0, 0, 6, 0],
        [8, 0, 0, 0, 6, 0, 0, 0, 3],
        [4, 0, 0, 8, 0, 3, 0, 0, 1],
        [7, 0, 0, 0, 2, 0, 0, 0, 6],
        [0, 6, 0, 0, 0, 0, 2, 8, 0],
        [0, 0, 0, 4, 1, 9, 0, 0, 5],
        [0, 0, 0, 0, 8, 0, 0, 7, 9],
    ];
    for row in 0..9 {
        for col in 0..9 {
            if clues[row][col] != 0 {
                let clue = terms.mk_int(BigInt::from(clues[row][col]));
                let eq = terms.mk_eq(cells[row][col], clue);
                atoms.push((eq, true));
            }
        }
    }

    for row in &cells {
        add_pairwise_disequalities(&mut terms, &mut atoms, row);
    }
    for col in 0..9 {
        let column: Vec<_> = (0..9).map(|row| cells[row][col]).collect();
        add_pairwise_disequalities(&mut terms, &mut atoms, &column);
    }
    for box_row in 0..3 {
        for box_col in 0..3 {
            let mut block = Vec::new();
            for row in (box_row * 3)..(box_row * 3 + 3) {
                for col in (box_col * 3)..(box_col * 3 + 3) {
                    block.push(cells[row][col]);
                }
            }
            add_pairwise_disequalities(&mut terms, &mut atoms, &block);
        }
    }

    let mut solver = LiaSolver::new(&terms);
    for (atom, value) in atoms {
        solver.assert_literal(atom, value);
    }

    assert!(matches!(solver.check(), TheoryResult::Sat));
    let model = solver
        .direct_enum_witness
        .as_ref()
        .expect("finite-domain search should store the Sudoku witness");
    for row in 0..9 {
        for col in 0..9 {
            let value = model
                .values
                .get(&cells[row][col])
                .expect("cell must have a value");
            assert!(value >= &BigInt::one() && value <= &BigInt::from(9));
            if clues[row][col] != 0 {
                assert_eq!(value, &BigInt::from(clues[row][col]));
            }
        }
    }
}

#[test]
fn test_lia_direct_enumeration_coefficient_explosion_guard_aborts() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));

    // Small coefficient: direct enumeration runs and detects UNSAT from non-integer solution.
    let lhs_small = terms.mk_mul(vec![two, x]);
    let eq_small = terms.mk_eq(lhs_small, one);
    let mut solver_small = LiaSolver::new(&terms);
    solver_small.assert_literal(eq_small, true);
    assert!(matches!(solver_small.lra.check(), TheoryResult::Sat));
    assert!(matches!(
        solver_small.try_direct_enumeration(),
        DirectEnumResult::Unsat(_)
    ));

    // Huge coefficient: scaling produces a rational constant with denominator > MAX_COEFF_BITS,
    // so the enumeration code aborts early instead of risking BigInt blowup.
    let huge_coeff = BigInt::one() << 300usize;
    assert!(huge_coeff.bits() > 256);
    let huge = terms.mk_int(huge_coeff);
    let lhs_huge = terms.mk_mul(vec![huge, x]);
    let eq_huge = terms.mk_eq(lhs_huge, one);
    let mut solver_huge = LiaSolver::new(&terms);
    solver_huge.assert_literal(eq_huge, true);
    assert!(matches!(solver_huge.lra.check(), TheoryResult::Sat));
    assert!(matches!(
        solver_huge.try_direct_enumeration(),
        DirectEnumResult::NoConclusion
    ));
}

#[test]
fn test_lia_direct_enumeration_system_05_returns_sat_witness() {
    // Regression test for #1911: system_05 used to fall back to 28+ branch-and-bound iterations
    // because direct enumeration refused to act when multiple integer solutions exist.
    let mut terms = TermStore::new();

    let v0 = terms.mk_var("v0", Sort::Int);
    let v1 = terms.mk_var("v1", Sort::Int);
    let v2 = terms.mk_var("v2", Sort::Int);
    let v3 = terms.mk_var("v3", Sort::Int);

    let c5 = terms.mk_int(BigInt::from(5));
    let c4 = terms.mk_int(BigInt::from(4));
    let c3 = terms.mk_int(BigInt::from(3));
    let c2 = terms.mk_int(BigInt::from(2));
    let c1 = terms.mk_int(BigInt::from(1));
    let c_1 = terms.mk_int(BigInt::from(-1));
    let c_2 = terms.mk_int(BigInt::from(-2));
    let c_3 = terms.mk_int(BigInt::from(-3));
    let c_4 = terms.mk_int(BigInt::from(-4));
    let c_5 = terms.mk_int(BigInt::from(-5));

    let k19 = terms.mk_int(BigInt::from(19));
    let k_41 = terms.mk_int(BigInt::from(-41));
    let k_14 = terms.mk_int(BigInt::from(-14));
    let k_16 = terms.mk_int(BigInt::from(-16));
    let k26 = terms.mk_int(BigInt::from(26));
    let k_47 = terms.mk_int(BigInt::from(-47));
    let k_48 = terms.mk_int(BigInt::from(-48));
    let k10 = terms.mk_int(BigInt::from(10));

    // (>= (+ (* 5 v0) (* -2 v1) (* 1 v2) (* -4 v3)) 19)
    let a0_0 = terms.mk_mul(vec![c5, v0]);
    let a0_1 = terms.mk_mul(vec![c_2, v1]);
    let a0_2 = terms.mk_mul(vec![c1, v2]);
    let a0_3 = terms.mk_mul(vec![c_4, v3]);
    let a0 = terms.mk_add(vec![a0_0, a0_1, a0_2, a0_3]);
    let ge0 = terms.mk_ge(a0, k19);

    // (>= (+ (* 5 v0) (* -3 v1) (* -1 v2) (* -3 v3)) -41)
    let a1_0 = terms.mk_mul(vec![c5, v0]);
    let a1_1 = terms.mk_mul(vec![c_3, v1]);
    let a1_2 = terms.mk_mul(vec![c_1, v2]);
    let a1_3 = terms.mk_mul(vec![c_3, v3]);
    let a1 = terms.mk_add(vec![a1_0, a1_1, a1_2, a1_3]);
    let ge1 = terms.mk_ge(a1, k_41);

    // (<= (+ (* -3 v0) (* -1 v1) (* 4 v2) (* 4 v3)) -14)
    let a2_0 = terms.mk_mul(vec![c_3, v0]);
    let a2_1 = terms.mk_mul(vec![c_1, v1]);
    let a2_2 = terms.mk_mul(vec![c4, v2]);
    let a2_3 = terms.mk_mul(vec![c4, v3]);
    let a2 = terms.mk_add(vec![a2_0, a2_1, a2_2, a2_3]);
    let le2 = terms.mk_le(a2, k_14);

    // (= (+ (* -4 v0) (* 2 v1) (* -1 v2) (* 1 v3)) -16)
    let a3_0 = terms.mk_mul(vec![c_4, v0]);
    let a3_1 = terms.mk_mul(vec![c2, v1]);
    let a3_2 = terms.mk_mul(vec![c_1, v2]);
    let a3_3 = terms.mk_mul(vec![c1, v3]);
    let a3 = terms.mk_add(vec![a3_0, a3_1, a3_2, a3_3]);
    let eq3 = terms.mk_eq(a3, k_16);

    // (>= (+ (* 3 v0) (* 2 v1) (* 2 v2) (* -4 v3)) 26)
    let a4_0 = terms.mk_mul(vec![c3, v0]);
    let a4_1 = terms.mk_mul(vec![c2, v1]);
    let a4_2 = terms.mk_mul(vec![c2, v2]);
    let a4_3 = terms.mk_mul(vec![c_4, v3]);
    let a4 = terms.mk_add(vec![a4_0, a4_1, a4_2, a4_3]);
    let ge4 = terms.mk_ge(a4, k26);

    // (>= (+ (* 1 v0) (* 4 v2) (* -1 v3)) -47)
    let a5_0 = terms.mk_mul(vec![c1, v0]);
    let a5_1 = terms.mk_mul(vec![c4, v2]);
    let a5_2 = terms.mk_mul(vec![c_1, v3]);
    let a5 = terms.mk_add(vec![a5_0, a5_1, a5_2]);
    let ge5 = terms.mk_ge(a5, k_47);

    // (= (+ (* -2 v0) (* 5 v1) (* 4 v2) (* 4 v3)) -48)
    let a6_0 = terms.mk_mul(vec![c_2, v0]);
    let a6_1 = terms.mk_mul(vec![c5, v1]);
    let a6_2 = terms.mk_mul(vec![c4, v2]);
    let a6_3 = terms.mk_mul(vec![c4, v3]);
    let a6 = terms.mk_add(vec![a6_0, a6_1, a6_2, a6_3]);
    let eq6 = terms.mk_eq(a6, k_48);

    // (= (+ (* -1 v0) (* 4 v1) (* -5 v2) (* -3 v3)) 10)
    let a7_0 = terms.mk_mul(vec![c_1, v0]);
    let a7_1 = terms.mk_mul(vec![c4, v1]);
    let a7_2 = terms.mk_mul(vec![c_5, v2]);
    let a7_3 = terms.mk_mul(vec![c_3, v3]);
    let a7 = terms.mk_add(vec![a7_0, a7_1, a7_2, a7_3]);
    let eq7 = terms.mk_eq(a7, k10);

    let mut solver = LiaSolver::new(&terms);
    for atom in [ge0, ge1, le2, eq3, ge4, ge5, eq6, eq7] {
        solver.assert_literal(atom, true);
    }

    let res = solver.check();
    assert!(matches!(res, TheoryResult::Sat));
    assert!(
        solver.direct_enum_witness.is_some(),
        "expected direct enumeration to produce a SAT witness"
    );

    let model = solver.extract_model().expect("SAT should have a model");

    for &(lit, asserted_value) in &solver.asserted {
        let TermData::App(Symbol::Named(name), args) = solver.terms.get(lit) else {
            panic!("Expected app term for asserted literal");
        };
        assert_eq!(args.len(), 2);
        let lhs = solver
            .evaluate_linear_expr(&model.values, args[0])
            .expect("lhs should be evaluable");
        let rhs = solver
            .evaluate_linear_expr(&model.values, args[1])
            .expect("rhs should be evaluable");

        let atom_holds = match name.as_str() {
            ">=" => lhs >= rhs,
            "<=" => lhs <= rhs,
            ">" => lhs > rhs,
            "<" => lhs < rhs,
            "=" => lhs == rhs,
            _ => panic!("Unexpected predicate: {name}"),
        };
        assert_eq!(
            atom_holds, asserted_value,
            "Model violated asserted literal {name} (lhs={lhs}, rhs={rhs})"
        );
    }
}

#[test]
fn test_hnf_coefficient_explosion_guard_aborts() {
    let huge_coeff = BigInt::one() << 300usize;
    assert!(huge_coeff.bits() > 256);

    let mut m = hnf::IntMatrix::new(1, 2);
    m.set(0, 0, BigInt::one());
    m.set(0, 1, huge_coeff);

    assert!(hnf::compute_hnf(&m, &BigInt::one()).is_none());
}

#[test]
fn test_lia_integer_bounds_farkas_certificate() {
    use num_rational::Rational64;
    let mut terms = TermStore::new();

    // x > 5 and x < 6 where x is integer - UNSAT
    // This should trigger check_integer_bounds_conflict and produce Farkas
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let six = terms.mk_int(BigInt::from(6));

    let gt_atom = terms.mk_gt(x, five); // x > 5
    let lt_atom = terms.mk_lt(x, six); // x < 6

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(gt_atom, true);
    solver.assert_literal(lt_atom, true);

    let result = solver.check();

    // Should be UnsatWithFarkas with valid coefficients
    match result {
        TheoryResult::UnsatWithFarkas(conflict) => {
            // Should have 2 conflicting literals (lower and upper bound)
            assert_eq!(
                conflict.literals.len(),
                2,
                "Expected 2 conflicting literals for bounds conflict"
            );
            // Should have Farkas annotation
            assert!(
                conflict.farkas.is_some(),
                "Expected Farkas annotation for integer bounds conflict"
            );
            let farkas = conflict.farkas.unwrap();
            // Both coefficients should be 1
            assert_eq!(farkas.coefficients.len(), 2);
            assert_eq!(farkas.coefficients[0], Rational64::from(1));
            assert_eq!(farkas.coefficients[1], Rational64::from(1));
            assert!(
                farkas.is_valid(),
                "Farkas coefficients should be non-negative"
            );
        }
        TheoryResult::Unsat(_) => {
            panic!("Expected UnsatWithFarkas but got Unsat without Farkas coefficients")
        }
        other => panic!("Expected Unsat but got {other:?}"),
    }
}

#[test]
fn test_lia_gcd_farkas_certificate() {
    use num_rational::Rational64;
    let mut terms = TermStore::new();

    // 2*x = 5 - GCD(2) = 2 doesn't divide 5, so UNSAT
    let x = terms.mk_var("x", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let five = terms.mk_int(BigInt::from(5));

    let two_x = terms.mk_mul(vec![two, x]);
    let eq = terms.mk_eq(two_x, five);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);

    let result = solver.check();

    // Should be UnsatWithFarkas
    match result {
        TheoryResult::UnsatWithFarkas(conflict) => {
            // Single equality as the reason
            assert_eq!(
                conflict.literals.len(),
                1,
                "Expected 1 conflicting literal for GCD failure"
            );
            // Should have Farkas annotation
            assert!(
                conflict.farkas.is_some(),
                "Expected Farkas annotation for GCD test failure"
            );
            let farkas = conflict.farkas.unwrap();
            // Single coefficient of 1
            assert_eq!(farkas.coefficients.len(), 1);
            assert_eq!(farkas.coefficients[0], Rational64::from(1));
        }
        TheoryResult::Unsat(_) => {
            panic!("Expected UnsatWithFarkas but got Unsat without Farkas coefficients")
        }
        other => panic!("Expected Unsat but got {other:?}"),
    }
}

/// #8124: Shared equality with constant expressions must report conflict,
/// not silently drop it.
///
/// When EUF propagates `5 = 3` (e.g., via a chain like f(x) = 5, f(x) = 3),
/// the combined expression after coefficient collection is empty with a
/// non-zero constant (5 - 3 = 2 != 0). Previously this was silently dropped
/// and the solver would return Unknown or Sat instead of UNSAT.
#[test]
fn test_shared_equality_constant_conflict_not_dropped() {
    let mut terms = TermStore::new();
    let five = terms.mk_int(BigInt::from(5));
    let three = terms.mk_int(BigInt::from(3));

    // Create a reason literal (simulating EUF equality chain)
    let reason_term = terms.mk_var("eq_reason", Sort::Bool);
    let reason = vec![TheoryLit::new(reason_term, true)];

    let mut solver = LiaSolver::new(&terms);

    // Tell LIA that 5 = 3 (impossible!) via shared equality
    solver.assert_shared_equality(five, three, &reason);

    // The conflict should be detected via propagate_equalities()
    let eq_result = solver.propagate_equalities();
    assert!(
        eq_result.conflict.is_some(),
        "Impossible constant shared equality (5 = 3) must report a conflict \
         via propagate_equalities(), got conflict=None"
    );
    let conflict = eq_result.conflict.unwrap();
    assert!(!conflict.is_empty(), "Conflict reasons must not be empty");
    // The conflict reasons should include the reason literal from EUF
    assert!(
        conflict.iter().any(|l| l.term == reason_term && l.value),
        "Conflict should include the EUF reason literal, got: {conflict:?}"
    );
}

/// #8124: Shared equality constant conflict is also detected via check().
#[test]
fn test_shared_equality_constant_conflict_detected_by_check() {
    let mut terms = TermStore::new();
    let five = terms.mk_int(BigInt::from(5));
    let three = terms.mk_int(BigInt::from(3));

    let reason_term = terms.mk_var("eq_reason", Sort::Bool);
    let reason = vec![TheoryLit::new(reason_term, true)];

    let mut solver = LiaSolver::new(&terms);
    solver.assert_shared_equality(five, three, &reason);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "Impossible constant shared equality (5 = 3) must be UNSAT via check(), got: {result:?}"
    );
    if let TheoryResult::Unsat(lits) = result {
        assert!(
            lits.iter().any(|l| l.term == reason_term && l.value),
            "Conflict should include the EUF reason literal, got: {lits:?}"
        );
    }
}

/// #8124: Shared equality constant conflict is also detected via check_during_propagate().
#[test]
fn test_shared_equality_constant_conflict_detected_by_check_during_propagate() {
    let mut terms = TermStore::new();
    let five = terms.mk_int(BigInt::from(5));
    let three = terms.mk_int(BigInt::from(3));

    let reason_term = terms.mk_var("eq_reason", Sort::Bool);
    let reason = vec![TheoryLit::new(reason_term, true)];

    let mut solver = LiaSolver::new(&terms);
    solver.assert_shared_equality(five, three, &reason);

    let result = solver.check_during_propagate();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "Impossible constant shared equality (5 = 3) must be UNSAT via \
         check_during_propagate(), got: {result:?}"
    );
}

/// #8124: After pop(), a shared equality conflict from the inner scope
/// must not persist.
#[test]
fn test_shared_equality_constant_conflict_cleared_on_pop() {
    let mut terms = TermStore::new();
    let five = terms.mk_int(BigInt::from(5));
    let three = terms.mk_int(BigInt::from(3));

    let reason_term = terms.mk_var("eq_reason", Sort::Bool);
    let reason = vec![TheoryLit::new(reason_term, true)];

    let mut solver = LiaSolver::new(&terms);
    solver.push();
    solver.assert_shared_equality(five, three, &reason);
    // Conflict is pending
    assert!(solver.pending_shared_eq_conflict.is_some());
    solver.pop();
    // After pop, conflict must be cleared
    assert!(
        solver.pending_shared_eq_conflict.is_none(),
        "Pending shared equality conflict must be cleared on pop()"
    );
    // check() should return Sat (empty problem)
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

/// #8124: Trivially true constant equality (5 = 5) must not create a conflict.
#[test]
fn test_shared_equality_constant_trivially_true() {
    let mut terms = TermStore::new();
    let five = terms.mk_int(BigInt::from(5));

    let reason_term = terms.mk_var("eq_reason", Sort::Bool);
    let reason = vec![TheoryLit::new(reason_term, true)];

    let mut solver = LiaSolver::new(&terms);
    solver.assert_shared_equality(five, five, &reason);

    // No conflict should be pending
    assert!(
        solver.pending_shared_eq_conflict.is_none(),
        "Trivially true equality (5 = 5) must not create a conflict"
    );
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

// --- #8823: LIA timings() real-measurement tests ---
//
// Before #8823, LiaSolver::timings() returned a static zero struct, so any
// dispatcher reading per-phase cost saw fake data. These tests pin the new
// contract: timings start at zero, simplex time accumulates after a real
// check(), and reset_timings() actually clears them.

#[test]
fn test_lia_timings_initially_zero() {
    let terms = TermStore::new();
    let solver = LiaSolver::new(&terms);
    let t = solver.timings();
    assert_eq!(
        t.simplex,
        std::time::Duration::ZERO,
        "fresh solver should report zero simplex time"
    );
    assert_eq!(t.gomory, std::time::Duration::ZERO);
    assert_eq!(t.hnf, std::time::Duration::ZERO);
    assert_eq!(t.dioph, std::time::Duration::ZERO);
}

#[test]
fn test_lia_timings_simplex_nonzero_after_check() {
    // Give the simplex something to actually do so the timed wrapper
    // records a non-zero duration even on very fast machines.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    // Use a domain wider than the finite-domain SAT witness shortcut so this
    // test specifically exercises the simplex timing path.
    let upper = terms.mk_int(BigInt::from(100));
    let x_ge = terms.mk_ge(x, zero);
    let y_ge = terms.mk_ge(y, zero);
    let x_le = terms.mk_le(x, upper);
    let y_le = terms.mk_le(y, upper);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(x_ge, true);
    solver.assert_literal(y_ge, true);
    solver.assert_literal(x_le, true);
    solver.assert_literal(y_le, true);

    // Before check(): still zero.
    assert_eq!(solver.timings().simplex, std::time::Duration::ZERO);

    let _ = solver.check();

    // After check(): simplex must have accumulated some measurable time,
    // or at least strictly more than the pre-check zero baseline. The
    // Instant::now() resolution is coarse on some platforms, so allow
    // strictly-greater-than-zero as the contract.
    let t = solver.timings();
    assert!(
        t.simplex > std::time::Duration::ZERO,
        "LIA simplex timing must be non-zero after check(), got {:?}",
        t.simplex
    );
}

#[test]
fn test_lia_reset_timings_clears_and_reaccumulates() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let x_ge = terms.mk_ge(x, zero);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(x_ge, true);
    let _ = solver.check();
    assert!(
        solver.timings().simplex > std::time::Duration::ZERO,
        "precondition: simplex time should be non-zero after first check"
    );

    solver.reset_timings();
    let t = solver.timings();
    assert_eq!(
        t.simplex,
        std::time::Duration::ZERO,
        "reset_timings() must clear simplex"
    );
    assert_eq!(t.gomory, std::time::Duration::ZERO);
    assert_eq!(t.hnf, std::time::Duration::ZERO);
    assert_eq!(t.dioph, std::time::Duration::ZERO);

    // Re-accumulates on subsequent checks. A single check on a one-constraint
    // problem can complete inside the clock's resolution and record exactly
    // ZERO, which made the single-shot form flaky in release (~1 in 20). Retry a
    // bounded number of times: re-accumulation is the property under test, and
    // any working accumulator crosses a nonzero duration well before the cap.
    let mut accumulated = std::time::Duration::ZERO;
    for _ in 0..100 {
        let _ = solver.check();
        accumulated = solver.timings().simplex;
        if accumulated > std::time::Duration::ZERO {
            break;
        }
    }
    assert!(
        accumulated > std::time::Duration::ZERO,
        "timings must re-accumulate after reset+check (100 checks still totalled zero)"
    );
}

#[test]
fn test_dioph_state_preserves_lia_and_lra_model_equality_proposals_8785() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let pair = if x.0 < y.0 { (x, y) } else { (y, x) };

    let mut solver = LiaSolver::new(&terms);
    solver.propagated_equality_pairs.insert(pair);

    let mut lra_pairs = HashSet::default();
    lra_pairs.insert(pair);
    solver
        .lra_solver_mut()
        .import_model_equality_proposal_state(lra_pairs, HashSet::default());

    let state = solver.take_dioph_state();
    assert!(state.propagated_equality_pairs.contains(&pair));
    assert!(state.lra_propagated_equality_pairs.contains(&pair));

    let mut restored = LiaSolver::new(&terms);
    restored.import_dioph_state(state);

    let restored_state = restored.take_dioph_state();
    assert!(restored_state.propagated_equality_pairs.contains(&pair));
    assert!(restored_state.lra_propagated_equality_pairs.contains(&pair));
}
