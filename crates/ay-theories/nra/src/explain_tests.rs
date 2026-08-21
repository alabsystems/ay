// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for conflict explanation.
//!
//! The load-bearing ones are the SOUNDNESS tests: a producer that returns a
//! clause which is not a theory consequence is a wrong `unsat`, and no gate in
//! this repository can catch that downstream.

use super::*;
use crate::mpbq::BqInterval;
use crate::subresultant::Mono;

fn ints(v: &[i64]) -> Vec<BigInt> {
    v.iter().map(|&x| BigInt::from(x)).collect()
}

fn rat(n: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(n))
}

fn ratq(n: i64, d: i64) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

/// A root of `p` isolated by the open dyadic interval `(lo, hi)`.
fn alg(p: &[i64], lo: i64, hi: i64) -> Anum {
    let iv = BqInterval::new(
        Bq::from_int(BigInt::from(lo)),
        Bq::from_int(BigInt::from(hi)),
    )
    .expect("lo < hi");
    Anum::from_poly_interval(&ints(p), &iv).expect("isolates one root")
}

fn lit(id: i32, p: &[i64], cond: SignCond, roots: Vec<Anum>) -> ConflictLit {
    ConflictLit {
        lit: id,
        p: ints(p),
        cond,
        roots,
    }
}

// ===========================================================================
// The gap this module works around, PINNED
// ===========================================================================

/// `IntervalSet::justification()` returns the EMPTY justification for an empty
/// set — in exactly the case its doc comment says a caller needs it for.
///
/// This is why `explain_univariate` tracks cited literals itself instead of
/// reading them back out of the emptied set. Pinned as a test so the workaround
/// is not quietly removed if the gap is ever closed.
#[test]
fn test_empty_intersection_loses_its_justification() {
    // `x < 0` justified by literal 1.
    let neg = ialg::from_sign_condition(
        &ints(&[0, 1]),
        &[Anum::rational(rat(0))],
        SignCond::Lt,
        Just::of(1).unwrap(),
    )
    .expect("built");
    // `x > 0` justified by literal 2.
    let pos = ialg::from_sign_condition(
        &ints(&[0, 1]),
        &[Anum::rational(rat(0))],
        SignCond::Gt,
        Just::of(2).unwrap(),
    )
    .expect("built");

    assert_eq!(neg.justification().unwrap().lits(), &[1]);
    assert_eq!(pos.justification().unwrap().lits(), &[2]);

    let meet = neg.intersect(&pos).expect("decided");
    assert!(meet.is_empty(), "x < 0 and x > 0 have no common point");

    // The conflict clause needs {1, 2}. The set reports NOTHING.
    assert_eq!(
        meet.justification().unwrap().lits(),
        &[] as &[i32],
        "an emptied set carries no justification -- the documented use is unserved"
    );
}

// ===========================================================================
// The checker: PROOFS
// ===========================================================================

/// `x < 0 /\ x > 0` is unsatisfiable, so `x >= 0 \/ x <= 0` is valid.
#[test]
fn test_valid_strict_opposite_bounds() {
    let ls = vec![
        lit(1, &[0, 1], SignCond::Lt, vec![Anum::rational(rat(0))]),
        lit(2, &[0, 1], SignCond::Gt, vec![Anum::rational(rat(0))]),
    ];
    assert_eq!(clause_is_valid(&ls), Some(true));
    assert_eq!(clause_countermodel(&ls), Some(None));
}

/// `x^2 - 2 > 0 /\ x^2 - 3 < 0` IS satisfiable — the annulus
/// `sqrt(2) < |x| < sqrt(3)`, e.g. `x = 3/2` — so the clause is NOT valid. The
/// counterexample is the whole point: `Some(false)` here must be witnessed, not
/// asserted.
#[test]
fn test_not_valid_has_a_countermodel() {
    // x^2 - 2, roots +-sqrt(2)
    let r2n = alg(&[-2, 0, 1], -2, -1);
    let r2p = alg(&[-2, 0, 1], 1, 2);
    // x^2 - 3, roots +-sqrt(3)
    let r3n = alg(&[-3, 0, 1], -2, -1);
    let r3p = alg(&[-3, 0, 1], 1, 2);

    let ls = vec![
        lit(1, &[-2, 0, 1], SignCond::Gt, vec![r2n, r2p]),
        lit(2, &[-3, 0, 1], SignCond::Lt, vec![r3n, r3p]),
    ];
    assert_eq!(clause_is_valid(&ls), Some(false));

    let cm = clause_countermodel(&ls)
        .expect("decided")
        .expect("witnessed");
    // The witness really does satisfy both literals.
    assert!(cm.sign_of_poly(&ints(&[-2, 0, 1])).unwrap() > 0);
    assert!(cm.sign_of_poly(&ints(&[-3, 0, 1])).unwrap() < 0);
}

/// The mirror of the case above, and the one that catches a decomposition
/// missing its OPEN cells: `x^2 - 2 < 0 /\ x^2 - 3 > 0` needs `|x| < sqrt(2)`
/// and `|x| > sqrt(3)` at once, which is empty. A checker that sampled only at
/// the roots would agree for the wrong reason; a checker that sampled only the
/// gaps would too. Both are needed, and this pins the conjunction of them.
#[test]
fn test_valid_nested_annuli_conflict() {
    let ls = vec![
        lit(
            1,
            &[-2, 0, 1],
            SignCond::Lt,
            vec![alg(&[-2, 0, 1], -2, -1), alg(&[-2, 0, 1], 1, 2)],
        ),
        lit(
            2,
            &[-3, 0, 1],
            SignCond::Gt,
            vec![alg(&[-3, 0, 1], -2, -1), alg(&[-3, 0, 1], 1, 2)],
        ),
    ];
    assert_eq!(clause_is_valid(&ls), Some(true));
    let e = explain_univariate(&ls).expect("conflict explained");
    assert_eq!(e.cited(), &[1, 2]);
}

/// `x^2 + 1 < 0` is unsatisfiable on its own: a positive-definite polynomial
/// with NO real roots. The whole line is one cell, and the single sample point
/// decides it.
#[test]
fn test_valid_rootless_positive_definite() {
    let ls = vec![lit(1, &[1, 0, 1], SignCond::Lt, vec![])];
    assert_eq!(clause_is_valid(&ls), Some(true));
}

/// `x^2 - 2 = 0 /\ x < 0 /\ x > -1` is unsatisfiable: the negative root of
/// `x^2 - 2` is `-sqrt(2) < -1`. This one genuinely needs the ALGEBRAIC sample
/// points -- a rational-only decomposition cannot see it.
#[test]
fn test_valid_algebraic_endpoint_conflict() {
    let rn = alg(&[-2, 0, 1], -2, -1);
    let rp = alg(&[-2, 0, 1], 1, 2);
    let ls = vec![
        lit(1, &[-2, 0, 1], SignCond::Eq, vec![rn, rp]),
        lit(2, &[0, 1], SignCond::Lt, vec![Anum::rational(rat(0))]),
        // x + 1 > 0  <=>  x > -1
        lit(3, &[1, 1], SignCond::Gt, vec![Anum::rational(rat(-1))]),
    ];
    assert_eq!(clause_is_valid(&ls), Some(true));
}

/// The same three literals with the bound moved out to `-2` ARE satisfiable at
/// `x = -sqrt(2)`, and the witness is irrational.
#[test]
fn test_not_valid_witness_is_irrational() {
    let rn = alg(&[-2, 0, 1], -2, -1);
    let rp = alg(&[-2, 0, 1], 1, 2);
    let ls = vec![
        lit(1, &[-2, 0, 1], SignCond::Eq, vec![rn, rp]),
        lit(2, &[0, 1], SignCond::Lt, vec![Anum::rational(rat(0))]),
        // x + 2 > 0  <=>  x > -2
        lit(3, &[2, 1], SignCond::Gt, vec![Anum::rational(rat(-2))]),
    ];
    assert_eq!(clause_is_valid(&ls), Some(false));
    let cm = clause_countermodel(&ls)
        .expect("decided")
        .expect("witnessed");
    assert!(!cm.is_rational(), "the only witness is -sqrt(2)");
    assert_eq!(cm.sign_of_poly(&ints(&[-2, 0, 1])).unwrap(), 0);
}

/// A conflict that is only visible AT a root: `x^2 - 2 >= 0 /\ x^2 - 2 <= 0`
/// forces `x = +-sqrt(2)`; adding `x != sqrt(2)` and `x != -sqrt(2)` empties it.
/// The root sample points are what decide this, not the gaps.
#[test]
fn test_valid_conflict_only_at_the_roots() {
    let rn = alg(&[-2, 0, 1], -2, -1);
    let rp = alg(&[-2, 0, 1], 1, 2);
    let ls = vec![
        lit(1, &[-2, 0, 1], SignCond::Ge, vec![rn.clone(), rp.clone()]),
        lit(2, &[-2, 0, 1], SignCond::Le, vec![rn, rp]),
        lit(
            3,
            &[-2, 0, 1],
            SignCond::Ne,
            vec![alg(&[-2, 0, 1], -2, -1), alg(&[-2, 0, 1], 1, 2)],
        ),
    ];
    assert_eq!(clause_is_valid(&ls), Some(true));
}

/// An empty clause is not valid. The permissive answer would be `true`.
#[test]
fn test_empty_clause_is_not_valid() {
    assert_eq!(clause_is_valid(&[]), Some(false));
}

// ===========================================================================
// The checker: root-list preconditions, verified in BOTH directions
// ===========================================================================

/// A DROPPED root must be refused, not silently accepted. This is the exact
/// shape that made a non-empty feasible set look empty for a previous lane.
#[test]
fn test_dropped_root_is_refused() {
    // x^2 - 1 has roots -1 and 1. Supply only 1.
    let ls = vec![lit(
        1,
        &[-1, 0, 1],
        SignCond::Lt,
        vec![Anum::rational(rat(1))],
    )];
    assert_eq!(
        clause_is_valid(&ls),
        None,
        "an incomplete root list must DECLINE, never certify"
    );
}

/// A SPURIOUS extra root is refused too -- the count catches it.
#[test]
fn test_spurious_root_is_refused() {
    let ls = vec![lit(
        1,
        &[-1, 0, 1],
        SignCond::Lt,
        vec![
            Anum::rational(rat(-1)),
            Anum::rational(rat(0)),
            Anum::rational(rat(1)),
        ],
    )];
    assert_eq!(clause_is_valid(&ls), None);
}

/// A list with the right COUNT but a value that is not a root is refused. Count
/// alone cannot see this: one real root swapped for one non-root keeps the
/// count. This is the test the producer's own precondition check would fail.
#[test]
fn test_right_count_wrong_values_is_refused() {
    let ls = vec![lit(
        1,
        &[-1, 0, 1],
        SignCond::Lt,
        vec![Anum::rational(rat(-1)), Anum::rational(rat(2))],
    )];
    assert_eq!(
        clause_is_valid(&ls),
        None,
        "2 is not a root of x^2 - 1; the count is right and the list is wrong"
    );
}

/// Out-of-order roots are refused.
#[test]
fn test_descending_roots_are_refused() {
    let ls = vec![lit(
        1,
        &[-1, 0, 1],
        SignCond::Lt,
        vec![Anum::rational(rat(1)), Anum::rational(rat(-1))],
    )];
    assert_eq!(clause_is_valid(&ls), None);
}

/// Literal id `0` is not a literal.
#[test]
fn test_zero_literal_is_refused() {
    let ls = vec![lit(0, &[0, 1], SignCond::Lt, vec![Anum::rational(rat(0))])];
    assert_eq!(clause_is_valid(&ls), None);
    assert_eq!(explain_univariate(&ls), None);
}

// ===========================================================================
// falsified-under-the-assignment
// ===========================================================================

#[test]
fn test_falsified_under_trail() {
    assert!(clause_is_falsified(&[-1, -2], &[1, 2, 3]));
    assert!(!clause_is_falsified(&[-1, -4], &[1, 2, 3]));
    assert!(
        !clause_is_falsified(&[1], &[1]),
        "1 is not the negation of 1"
    );
    assert!(!clause_is_falsified(&[0], &[1]), "0 is not a literal");
}

// ===========================================================================
// The producer
// ===========================================================================

/// The headline case: two contradictory strict bounds produce a two-literal
/// clause, and the clause is false under the trail.
#[test]
fn test_explain_opposite_strict_bounds() {
    let ls = vec![
        lit(1, &[0, 1], SignCond::Lt, vec![Anum::rational(rat(0))]),
        lit(2, &[0, 1], SignCond::Gt, vec![Anum::rational(rat(0))]),
    ];
    let e = explain_univariate(&ls).expect("conflict explained");
    assert_eq!(e.len(), 2);
    assert_eq!(e.cited(), &[1, 2]);
    assert_eq!(e.lits(), &[-1, -2]);
    assert!(clause_is_falsified(e.lits(), &[1, 2]));
    // And, re-derived rather than trusted:
    let sub: Vec<ConflictLit> = ls
        .iter()
        .filter(|l| e.cited().contains(&l.lit))
        .cloned()
        .collect();
    assert_eq!(clause_is_valid(&sub), Some(true));
}

/// NO conflict must produce NO clause. Inventing one here prunes a satisfiable
/// region -- the wrong-`unsat` failure mode.
#[test]
fn test_no_conflict_no_clause() {
    let ls = vec![
        lit(1, &[0, 1], SignCond::Gt, vec![Anum::rational(rat(0))]),
        lit(2, &[-5, 1], SignCond::Lt, vec![Anum::rational(rat(5))]),
    ];
    assert!(
        explain_univariate(&ls).is_none(),
        "0 < x < 5 is satisfiable"
    );
}

/// An algebraic conflict: `x^2 - 2 > 0 /\ x > 0 /\ x < sqrt(2)`.
#[test]
fn test_explain_algebraic_conflict() {
    let rn = alg(&[-2, 0, 1], -2, -1);
    let rp = alg(&[-2, 0, 1], 1, 2);
    let ls = vec![
        lit(1, &[-2, 0, 1], SignCond::Gt, vec![rn.clone(), rp.clone()]),
        lit(2, &[0, 1], SignCond::Gt, vec![Anum::rational(rat(0))]),
        lit(3, &[-2, 0, 1], SignCond::Lt, vec![rn, rp]),
    ];
    let e = explain_univariate(&ls).expect("conflict explained");
    assert!(clause_is_falsified(e.lits(), &[1, 2, 3]));
    let sub: Vec<ConflictLit> = ls
        .iter()
        .filter(|l| e.cited().contains(&l.lit))
        .cloned()
        .collect();
    assert_eq!(clause_is_valid(&sub), Some(true));
}

/// Minimization drops the literal that plays no part. `x > 0`, `x < 0` conflict
/// on their own; `x < 100` is irrelevant and must not survive into the clause.
#[test]
fn test_minimization_drops_the_irrelevant_literal() {
    let ls = vec![
        lit(1, &[0, 1], SignCond::Gt, vec![Anum::rational(rat(0))]),
        lit(2, &[-100, 1], SignCond::Lt, vec![Anum::rational(rat(100))]),
        lit(3, &[0, 1], SignCond::Lt, vec![Anum::rational(rat(0))]),
    ];
    let e = explain_univariate(&ls).expect("conflict explained");
    assert_eq!(
        e.cited(),
        &[1, 3],
        "literal 2 is irrelevant and was dropped"
    );
    assert_eq!(e.len(), 2);
}

/// Every literal in a minimized clause is NECESSARY: dropping any one leaves a
/// satisfiable conjunction. This is the property minimization claims, checked
/// directly rather than by counting.
#[test]
fn test_minimized_clause_is_irredundant() {
    let ls = vec![
        lit(1, &[0, 1], SignCond::Gt, vec![Anum::rational(rat(0))]),
        lit(2, &[-100, 1], SignCond::Lt, vec![Anum::rational(rat(100))]),
        lit(3, &[0, 1], SignCond::Lt, vec![Anum::rational(rat(0))]),
    ];
    let e = explain_univariate(&ls).expect("conflict explained");
    let kept: Vec<ConflictLit> = ls
        .iter()
        .filter(|l| e.cited().contains(&l.lit))
        .cloned()
        .collect();
    for drop in 0..kept.len() {
        let smaller: Vec<ConflictLit> = kept
            .iter()
            .enumerate()
            .filter(|&(i, _)| i != drop)
            .map(|(_, l)| l.clone())
            .collect();
        assert_ne!(
            clause_is_valid(&smaller),
            Some(true),
            "literal {drop} was not necessary -- minimization left a redundant clause"
        );
    }
}

/// The producer refuses a conflict citing more than the ceiling.
#[test]
fn test_over_ceiling_declines() {
    let many: Vec<ConflictLit> = (1..=(MAX_CONFLICT_LITS as i32 + 1))
        .map(|i| lit(i, &[0, 1], SignCond::Lt, vec![Anum::rational(rat(0))]))
        .collect();
    assert_eq!(explain_univariate(&many), None);
    assert_eq!(clause_is_valid(&many), None);
}

// ===========================================================================
// sample points
// ===========================================================================

#[test]
fn test_sample_points_count_and_order() {
    let roots = vec![
        Anum::rational(rat(-1)),
        Anum::rational(rat(0)),
        Anum::rational(rat(1)),
    ];
    let s = sample_points(&roots).expect("built");
    assert_eq!(s.len(), 2 * roots.len() + 1);
    for w in s.windows(2) {
        assert_eq!(
            w[0].cmp_anum(&w[1]),
            Some(Ordering::Less),
            "sample points must strictly ascend"
        );
    }
}

#[test]
fn test_sample_points_no_roots() {
    let s = sample_points(&[]).expect("built");
    assert_eq!(s.len(), 1);
}

/// Between two irrational roots that are close together, the separator is still
/// found and is strictly between them.
#[test]
fn test_strictly_between_irrationals() {
    let a = alg(&[-2, 0, 1], 1, 2); // sqrt(2)  ~ 1.41421
    let b = alg(&[-3, 0, 1], 1, 2); // sqrt(3)  ~ 1.73205
    let m = strictly_between(&a, &b).expect("separated");
    let ma = Anum::rational(m);
    assert_eq!(a.cmp_anum(&ma), Some(Ordering::Less));
    assert_eq!(ma.cmp_anum(&b), Some(Ordering::Less));
}

/// Rational / algebraic mixed, and in the order that needs refinement.
#[test]
fn test_strictly_between_rational_and_algebraic() {
    let a = Anum::rational(ratq(7, 5)); // 1.4 < sqrt(2)
    let b = alg(&[-2, 0, 1], 1, 2);
    let m = strictly_between(&a, &b).expect("separated");
    let ma = Anum::rational(m);
    assert_eq!(a.cmp_anum(&ma), Some(Ordering::Less));
    assert_eq!(ma.cmp_anum(&b), Some(Ordering::Less));
}

/// Equal values exhaust the ladder and DECLINE. Never a spin, never a guess.
#[test]
fn test_strictly_between_equal_declines() {
    let a = Anum::rational(rat(1));
    let b = Anum::rational(rat(1));
    assert_eq!(strictly_between(&a, &b), None);
}

// ===========================================================================
// projection
// ===========================================================================

fn bip(x_coeffs: &[&[(u32, i64)]]) -> RPoly<MPolyZ> {
    RPoly::from_coeffs(
        x_coeffs
            .iter()
            .map(|terms| {
                MPolyZ::from_terms(
                    terms
                        .iter()
                        .map(|&(e, c)| (Mono::var_pow(0, e), BigInt::from(c)))
                        .collect(),
                )
            })
            .collect(),
    )
}

/// The projection of `x^2 - y` (a parabola) and `x - y` (a line): leading
/// coefficients, discriminants, and the one resultant.
#[test]
fn test_project_parabola_and_line() {
    // x^2 - y   ->  coeffs in x: [-y, 0, 1]
    let p = bip(&[&[(1, -1)], &[], &[(0, 1)]]);
    // x - y     ->  coeffs in x: [-y, 1]
    let q = bip(&[&[(1, -1)], &[(0, 1)]]);
    let proj = project(&[p, q], &[(0, 1)]).expect("projected");

    // Two leading coefficients, two discriminants, one resultant.
    assert_eq!(proj.factors.len(), 5);
    assert!(proj
        .factors
        .iter()
        .any(|f| f.kind == ProjKind::Resultant(0, 1)));
    // Res_x(x^2 - y, x - y) = y^2 - y, degree 2 -- the resultant is where the
    // parabola meets the line.
    let res = proj
        .factors
        .iter()
        .find(|f| f.kind == ProjKind::Resultant(0, 1))
        .expect("resultant present");
    assert_eq!(mpoly_total_degree(&res.poly), 2);
}

/// Degree growth is the headline projection cost. A resultant of two degree-`d`
/// polynomials in `x` with degree-`e` coefficients has degree up to `2 * d * e`:
/// the projection RAISES degree, and this pins how much on a concrete case.
#[test]
fn test_projection_raises_degree() {
    // x^2 - y^2  and  x^2 + y^2 - 4 : both total degree 2.
    let p = bip(&[&[(2, -1)], &[], &[(0, 1)]]);
    let q = bip(&[&[(2, 1), (0, -4)], &[], &[(0, 1)]]);
    let proj = project(&[p, q], &[(0, 1)]).expect("projected");
    assert_eq!(proj.in_max_total_degree, 2);
    assert!(
        proj.out_max_total_degree > proj.in_max_total_degree,
        "projection must raise degree: {} -> {}",
        proj.in_max_total_degree,
        proj.out_max_total_degree
    );
}

/// `relevant_pairs` keeps ADJACENT owners and drops the pair separated by a
/// third polynomial's root.
#[test]
fn test_relevant_pairs_adjacency() {
    // roots at 0 (lit 1), 1 (lit 2), 2 (lit 3): 1-2 and 2-3 adjacent, 1-3 not.
    let ls = vec![
        lit(1, &[0, 1], SignCond::Eq, vec![Anum::rational(rat(0))]),
        lit(2, &[-1, 1], SignCond::Eq, vec![Anum::rational(rat(1))]),
        lit(3, &[-2, 1], SignCond::Eq, vec![Anum::rational(rat(2))]),
    ];
    let pairs = relevant_pairs(&ls).expect("computed");
    assert!(pairs.contains(&(0, 1)));
    assert!(pairs.contains(&(1, 2)));
    assert!(
        !pairs.contains(&(0, 2)),
        "0 and 2 are separated by literal 2's root; their crossing is covered"
    );
}

#[test]
fn test_relevant_pairs_no_roots_no_pairs() {
    let ls = vec![lit(1, &[1, 0, 1], SignCond::Gt, vec![])];
    assert_eq!(relevant_pairs(&ls), Some(vec![]));
}

#[test]
fn test_degree_in_and_lc_sign() {
    let p = MPolyZ::from_terms(vec![(Mono::var_pow(0, 3), BigInt::one())]);
    assert_eq!(degree_in(&p, 0), 3);
    assert_eq!(degree_in(&p, 1), 0);
    assert_eq!(lc_sign(&ints(&[1, 2, -3])), -1);
    assert_eq!(lc_sign(&ints(&[1, 2, 3])), 1);
    assert_eq!(lc_sign(&ints(&[0, 0])), 0);
}
