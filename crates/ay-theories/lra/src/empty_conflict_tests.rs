// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::term::TermId;
use ay_core::{assert_conflict_soundness, Sort};

#[test]
fn test_dual_simplex_contradictory_sentinel_bounds_returns_unknown() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);

    solver.vars.push(VarInfo {
        value: InfRational::from_rational(BigRational::from(BigInt::from(0))),
        lower: Some(Bound::new(
            BigRational::from(BigInt::from(1)).into(),
            vec![TermId::SENTINEL],
            vec![true],
            Vec::new(),
            false,
        )),
        upper: Some(Bound::new(
            BigRational::from(BigInt::from(0)).into(),
            vec![TermId::SENTINEL],
            vec![true],
            Vec::new(),
            false,
        )),
        status: Some(VarStatus::NonBasic),
    });

    let result = solver.dual_simplex_with_max_iters(16);
    assert!(
        matches!(result, TheoryResult::Unknown),
        "Contradictory bounds with sentinel-only reasons must degrade to Unknown, got {result:?}"
    );
}

#[test]
fn test_dual_simplex_unpivotable_sentinel_conflict_returns_unknown() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);

    solver.vars = vec![
        VarInfo {
            value: InfRational::from_rational(BigRational::from(BigInt::from(0))),
            lower: None,
            upper: Some(Bound::new(
                BigRational::from(BigInt::from(0)).into(),
                vec![TermId::SENTINEL],
                vec![true],
                Vec::new(),
                false,
            )),
            status: Some(VarStatus::NonBasic),
        },
        VarInfo {
            value: InfRational::from_rational(BigRational::from(BigInt::from(0))),
            lower: Some(Bound::new(
                BigRational::from(BigInt::from(1)).into(),
                vec![TermId::SENTINEL],
                vec![true],
                Vec::new(),
                false,
            )),
            upper: None,
            status: Some(VarStatus::Basic(0)),
        },
    ];
    solver.rows = vec![TableauRow::new(
        1,
        vec![(0, BigRational::from(BigInt::from(1)))],
        BigRational::from(BigInt::from(0)),
    )];

    let result = solver.dual_simplex_with_max_iters(16);
    assert!(
        matches!(result, TheoryResult::Unknown),
        "Unpivotable row with sentinel-only reasons must degrade to Unknown, got {result:?}"
    );
}

#[test]
fn test_dual_simplex_nonbasic_contradiction_degrades_or_uses_row_conflict() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);

    let sentinel = TermId::SENTINEL;
    let row_reason = TermId::new(7);

    solver.vars = vec![
        VarInfo {
            value: InfRational::from_rational(BigRational::from(BigInt::from(0))),
            lower: Some(Bound::new(
                BigRational::from(BigInt::from(1)).into(),
                vec![sentinel],
                vec![true],
                Vec::new(),
                false,
            )),
            upper: Some(Bound::new(
                BigRational::from(BigInt::from(0)).into(),
                vec![sentinel],
                vec![true],
                Vec::new(),
                false,
            )),
            status: Some(VarStatus::NonBasic),
        },
        VarInfo {
            value: InfRational::from_rational(BigRational::from(BigInt::from(0))),
            lower: None,
            upper: Some(Bound::new(
                BigRational::from(BigInt::from(0)).into(),
                vec![row_reason],
                vec![true],
                Vec::new(),
                false,
            )),
            status: Some(VarStatus::Basic(0)),
        },
    ];

    solver.rows = vec![TableauRow::new(
        1,
        vec![(0, BigRational::from(BigInt::from(1)))],
        BigRational::from(BigInt::from(0)),
    )];

    let result = solver.dual_simplex_with_max_iters(16);
    match result {
        TheoryResult::UnsatWithFarkas(conflict) => {
            assert!(
                !conflict.literals.is_empty(),
                "row-derived conflict must not be empty"
            );
            assert!(
                conflict.literals.iter().any(|lit| lit.term == row_reason),
                "expected row-derived conflict to include non-sentinel reason"
            );
        }
        TheoryResult::Unknown => {
            // Current precheck behavior may degrade sentinel-only contradictory
            // non-basic bounds to Unknown before row-level conflict extraction.
        }
        other => {
            assert!(
                matches!(other, TheoryResult::Unknown),
                "expected UnsatWithFarkas or Unknown, got {other:?}"
            );
        }
    }
}

#[test]
fn test_dual_simplex_missing_active_bound_reasons_returns_unknown() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);

    let lower_reason = TermId::new(5);

    solver.vars = vec![
        VarInfo {
            value: InfRational::from_rational(BigRational::from(BigInt::from(0))),
            lower: Some(Bound::new(
                BigRational::from(BigInt::from(-10)).into(),
                vec![lower_reason],
                vec![true],
                Vec::new(),
                false,
            )),
            upper: Some(Bound::without_reasons(
                BigRational::from(BigInt::from(0)).into(),
                false,
            )),
            status: Some(VarStatus::NonBasic),
        },
        VarInfo {
            value: InfRational::from_rational(BigRational::from(BigInt::from(0))),
            // No basic-bound reasons so the row infeasibility precheck yields
            // no clause and the main loop reaches build_conflict_with_farkas().
            lower: Some(Bound::without_reasons(
                BigRational::from(BigInt::from(1)).into(),
                false,
            )),
            upper: None,
            status: Some(VarStatus::Basic(0)),
        },
    ];
    solver.rows = vec![TableauRow::new(
        1,
        vec![(0, BigRational::from(BigInt::from(1)))],
        BigRational::from(BigInt::from(0)),
    )];

    let result = solver.dual_simplex_with_max_iters(16);
    assert!(
        matches!(result, TheoryResult::Unknown),
        "Missing active-bound reasons must degrade to Unknown, got {result:?}"
    );
}

#[test]
fn test_contradictory_bounds_precheck_mixed_sentinel_real_returns_partial_conflict() {
    // Regression for #6679: contradictory-bounds precheck with one sentinel-only
    // axiom bound and one real-reason bound. Sentinel-only axioms are safe to
    // omit from the returned conflict, so the real literal must survive as a
    // partial conflict instead of degrading to Unknown.
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);

    let real_reason = TermId::new(7);
    solver.vars.push(VarInfo {
        value: InfRational::from_rational(BigRational::from(BigInt::from(0))),
        // lower = 1, sentinel-only reason
        lower: Some(Bound::new(
            BigRational::from(BigInt::from(1)).into(),
            vec![TermId::SENTINEL],
            vec![true],
            Vec::new(),
            false,
        )),
        // upper = 0, real reason → contradicts lower
        upper: Some(Bound::new(
            BigRational::from(BigInt::from(0)).into(),
            vec![real_reason],
            vec![true],
            Vec::new(),
            false,
        )),
        status: Some(VarStatus::NonBasic),
    });
    // #8764: stale-reason guard requires the real reason to be asserted.
    solver.asserted.insert(real_reason, true);

    let result = solver.dual_simplex_with_max_iters(16);
    match result {
        TheoryResult::UnsatWithFarkas(c) => assert_partial_conflict(&c.literals, real_reason),
        TheoryResult::Unsat(lits) => assert_partial_conflict(&lits, real_reason),
        other => panic!(
            "expected partial conflict from mixed sentinel/real contradictory bounds, got {other:?}"
        ),
    }
}

#[test]
fn test_contradictory_bounds_precheck_one_reasonless_returns_unknown() {
    // Regression for #4919: contradictory-bounds precheck where the lower
    // bound has no reasons at all (reasonless). The conflict needs both bounds
    // so returning only the upper-bound reasons is unsound.
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);

    let real_reason = TermId::new(42);
    solver.vars.push(VarInfo {
        value: InfRational::from_rational(BigRational::from(BigInt::from(0))),
        // lower = 5, no reasons at all (derived bound without tracking)
        lower: Some(Bound::without_reasons(
            BigRational::from(BigInt::from(5)).into(),
            false,
        )),
        // upper = 2, real reason → contradicts lower
        upper: Some(Bound::new(
            BigRational::from(BigInt::from(2)).into(),
            vec![real_reason],
            vec![true],
            Vec::new(),
            false,
        )),
        status: Some(VarStatus::NonBasic),
    });

    let result = solver.dual_simplex_with_max_iters(16);
    assert!(
        matches!(result, TheoryResult::Unknown),
        "Contradictory bounds with one reasonless side must degrade to Unknown, got {result:?}"
    );
}

#[test]
fn test_dual_simplex_reasonless_active_bound_conflict_is_never_semantically_sat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::from(BigInt::from(0)));
    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));
    let y_ge_one = terms.mk_ge(y, one);
    let _x_le_zero = terms.mk_le(x, zero);

    let mut solver = LraSolver::new(&terms);
    solver.vars = vec![
        VarInfo {
            value: InfRational::from_rational(BigRational::from(BigInt::from(0))),
            lower: Some(Bound::new(
                BigRational::from(BigInt::from(-10)).into(),
                vec![y_ge_one],
                vec![true],
                Vec::new(),
                false,
            )),
            upper: Some(Bound::without_reasons(
                BigRational::from(BigInt::from(0)).into(),
                false,
            )),
            status: Some(VarStatus::NonBasic),
        },
        VarInfo {
            value: InfRational::from_rational(BigRational::from(BigInt::from(0))),
            lower: Some(Bound::without_reasons(
                BigRational::from(BigInt::from(1)).into(),
                false,
            )),
            upper: None,
            status: Some(VarStatus::Basic(0)),
        },
    ];
    solver.rows = vec![TableauRow::new(
        1,
        vec![(0, BigRational::from(BigInt::from(1)))],
        BigRational::from(BigInt::from(0)),
    )];

    match solver.dual_simplex_with_max_iters(16) {
        TheoryResult::Unknown => {}
        result @ TheoryResult::Unsat(_) | result @ TheoryResult::UnsatWithFarkas(_) => {
            let conflict = assert_conflict_soundness(result, LraSolver::new(&terms));
            assert!(
                conflict.iter().any(|lit| lit.term == y_ge_one),
                "expected replayed conflict to retain the real lower-bound atom: {conflict:?}"
            );
        }
        other => panic!("expected Unknown or UNSAT conflict, got {other:?}"),
    }
}

fn assert_partial_conflict(lits: &[TheoryLit], expected_term: TermId) {
    assert!(!lits.is_empty(), "partial conflict must not be empty");
    assert!(
        lits.iter().any(|lit| lit.term == expected_term),
        "partial conflict must include expected reason: {lits:?}"
    );
    assert!(
        lits.iter().all(|lit| !lit.term.is_sentinel()),
        "partial conflict must not contain sentinels: {lits:?}"
    );
}

fn bi(n: i64) -> BigRational {
    BigRational::from(BigInt::from(n))
}

#[test]
fn test_sentinel_only_axiom_bound_produces_partial_conflict_not_unknown() {
    // Setup: y = x, x <= 0 (sentinel axiom), y >= 1 (real reason).
    // Infeasibility requires both; partial conflict keeps the real literal.
    let mut terms = TermStore::new();
    let y_term = terms.mk_var("y", Sort::Real);
    let one = terms.mk_rational(bi(1));
    let y_ge_1 = terms.mk_ge(y_term, one);

    let mut solver = LraSolver::new(&terms);
    solver.vars.push(VarInfo {
        value: InfRational::from_rational(bi(0)),
        lower: None,
        upper: Some(Bound::new(
            bi(0).into(),
            vec![TermId::SENTINEL],
            vec![true],
            Vec::new(),
            false,
        )),
        status: Some(VarStatus::NonBasic),
    });
    solver.vars.push(VarInfo {
        value: InfRational::from_rational(bi(0)),
        lower: Some(Bound::new(
            bi(1).into(),
            vec![y_ge_1],
            vec![true],
            Vec::new(),
            false,
        )),
        upper: None,
        status: Some(VarStatus::Basic(0)),
    });
    solver.rows = vec![TableauRow::new(1, vec![(0, bi(1))], bi(0))];
    // #8764: stale-reason guard requires the real reason to be asserted.
    solver.asserted.insert(y_ge_1, true);

    match solver.dual_simplex_with_max_iters(16) {
        TheoryResult::UnsatWithFarkas(c) => assert_partial_conflict(&c.literals, y_ge_1),
        TheoryResult::Unsat(lits) => assert_partial_conflict(&lits, y_ge_1),
        other => panic!(
            "expected UnsatWithFarkas or Unsat with partial conflict, got {other:?}; \
             sentinel-only bounds must produce a partial conflict, not degrade to Unknown"
        ),
    }
}

#[test]
fn test_unjustified_patch_bound_retracted_instead_of_unknown_livelock_a2() {
    // #A2 (conflict_without_literals livelock): a bound justified by a
    // pseudo-atom that is NEVER asserted (e.g. an NIA model-patch cut whose
    // "reason" is the monomial term `(* x x)` itself) makes the conflict
    // explanation fail the #8764 stale-reason guard, producing an EMPTY
    // conflict. dual_simplex used to return Unknown, and the outer DPLL(T)/
    // PDR loop re-queried the identical tableau thousands of times per run.
    //
    // The fix retracts the unjustified bound (sound: only relaxes the LP)
    // and continues the simplex, which here reaches Sat.
    let mut terms = TermStore::new();
    let x_term = terms.mk_var("x", Sort::Int);
    let prod_term = terms.mk_mul(vec![x_term, x_term]); // pseudo-atom: Int-sorted, never asserted
    let one = terms.mk_int(BigInt::from(1));
    let x_ge_1 = terms.mk_ge(x_term, one);

    let mut solver = LraSolver::new(&terms);
    // var 0 (non-basic, x): lower bound 1 with a REAL asserted reason.
    solver.vars.push(VarInfo {
        value: InfRational::from_rational(bi(1)),
        lower: Some(Bound::new(
            bi(1).into(),
            vec![x_ge_1],
            vec![true],
            Vec::new(),
            false,
        )),
        upper: None,
        status: Some(VarStatus::NonBasic),
    });
    // var 1 (basic, the monomial aux): fixed [0,0] by an NIA-style patch cut
    // whose only reason is the (never-asserted) product term.
    solver.vars.push(VarInfo {
        value: InfRational::from_rational(bi(1)),
        lower: Some(Bound::new(
            bi(0).into(),
            vec![prod_term],
            vec![true],
            Vec::new(),
            false,
        )),
        upper: Some(Bound::new(
            bi(0).into(),
            vec![prod_term],
            vec![true],
            Vec::new(),
            false,
        )),
        status: Some(VarStatus::Basic(0)),
    });
    // Row: basic var 1 = 1 * var 0  (value 1, violating its [0,0] bounds).
    solver.rows = vec![TableauRow::new(1, vec![(0, bi(1))], bi(0))];
    solver.asserted.insert(x_ge_1, true);

    let result = solver.dual_simplex_with_max_iters(16);
    assert!(
        matches!(result, TheoryResult::Sat),
        "unjustified patch bound must be retracted (relaxing the LP to Sat), \
         not degrade to a livelock-inducing Unknown; got {result:?}"
    );
    assert!(
        solver.stats.unjustified_bound_retractions >= 1,
        "expected at least one unjustified-bound retraction, got {}",
        solver.stats.unjustified_bound_retractions
    );
    // The retraction must be trail-recorded so scope pops restore it.
    assert!(
        !solver.trail.is_empty(),
        "retraction must be recorded on the bound trail for pop()"
    );
}

mod full_scan;
