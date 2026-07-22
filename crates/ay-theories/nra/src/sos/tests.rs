// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the rational SOS / Positivstellensatz certificate search and
//! the independent checker. The checker tests deliberately tamper with valid
//! certificates and require rejection.

use super::*;
use crate::univariate::{MultiConstraint, MultiPoly, Rel};
use ay_core::term::TermId;
use num_bigint::BigInt;
use num_rational::BigRational;

fn v(n: u32) -> TermId {
    TermId(n)
}

fn r(n: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(n))
}

fn rf(n: i64, d: i64) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

/// Build a polynomial from `(monomial vars, integer coeff)` pairs.
fn poly(terms: &[(&[TermId], i64)]) -> MultiPoly {
    let mut p = MultiPoly::zero();
    for (m, c) in terms {
        let mut mm = m.to_vec();
        mm.sort_unstable();
        p.add_term(mm, r(*c));
    }
    p
}

fn con(poly: MultiPoly, rel: Rel) -> MultiConstraint {
    MultiConstraint { poly, rel }
}

// ---------------------------------------------------------------------------
// PSD test.
// ---------------------------------------------------------------------------

#[test]
fn psd_identity_and_zero_pivots() {
    // Identity is PSD.
    assert!(is_psd(&[vec![r(1), r(0)], vec![r(0), r(1)]]));
    // Zero matrix is PSD.
    assert!(is_psd(&[vec![r(0), r(0)], vec![r(0), r(0)]]));
    // Rank-1 PSD: [[1,1],[1,1]] = (x+y)^2 Gram.
    assert!(is_psd(&[vec![r(1), r(1)], vec![r(1), r(1)]]));
    // Zero pivot with a clean (all-zero) trailing row/col is PSD.
    assert!(is_psd(&[vec![r(0), r(0)], vec![r(0), r(3)]]));
}

#[test]
fn not_psd_cases() {
    // Negative diagonal.
    assert!(!is_psd(&[vec![r(-1), r(0)], vec![r(0), r(1)]]));
    // Zero diagonal with a nonzero off-diagonal ⇒ 2x2 minor −a² < 0.
    assert!(!is_psd(&[vec![r(0), r(1)], vec![r(1), r(0)]]));
    // Indefinite: [[1,2],[2,1]] has determinant −3.
    assert!(!is_psd(&[vec![r(1), r(2)], vec![r(2), r(1)]]));
    // 3x3 with a negative Schur complement.
    assert!(!is_psd(&[
        vec![r(1), r(0), r(0)],
        vec![r(0), r(1), r(2)],
        vec![r(0), r(2), r(1)],
    ]));
}

// ---------------------------------------------------------------------------
// Hand-built certificate + tamper tests.
// ---------------------------------------------------------------------------

/// `{ x ≥ 1, x ≤ 0 }` with the linear Farkas certificate `(x−1) + (−x) = −1`.
fn linear_farkas_setup() -> (Vec<MultiConstraint>, SosCertificate) {
    let x = v(1);
    // c0: x ≥ 1  →  x − 1 ≥ 0
    let c0 = con(poly(&[(&[x], 1), (&[], -1)]), Rel::Ge);
    // c1: x ≤ 0  →  x ≤ 0  (orients to −x ≥ 0)
    let c1 = con(poly(&[(&[x], 1)]), Rel::Le);
    let constraints = vec![c0, c1];
    // basis [1, x], σ0 = 0.
    let cert = SosCertificate {
        basis: vec![vec![], vec![x]],
        gram: vec![vec![r(0), r(0)], vec![r(0), r(0)]],
        terms: vec![
            CertTerm {
                origin: CertOrigin::Constraint(0),
                multiplier: r(1),
            },
            CertTerm {
                origin: CertOrigin::Constraint(1),
                multiplier: r(1),
            },
        ],
        rhs: r(-1),
    };
    (constraints, cert)
}

#[test]
fn hand_linear_farkas_verifies() {
    let (constraints, cert) = linear_farkas_setup();
    assert_eq!(cert.verify(&constraints), Ok(()));
}

#[test]
fn tamper_multiplier_rejected() {
    let (constraints, mut cert) = linear_farkas_setup();
    // Break the identity by scaling one multiplier.
    cert.terms[0].multiplier = r(2);
    assert_eq!(cert.verify(&constraints), Err(SosError::IdentityMismatch));
}

#[test]
fn tamper_negative_multiplier_rejected() {
    let (constraints, mut cert) = linear_farkas_setup();
    // Negate a multiplier: identity still off AND the sign check fires first
    // for an inequality term.
    cert.terms[0].multiplier = r(-1);
    assert_eq!(cert.verify(&constraints), Err(SosError::NegativeMultiplier));
}

#[test]
fn tamper_rhs_positive_rejected() {
    let (constraints, mut cert) = linear_farkas_setup();
    cert.rhs = r(1);
    assert_eq!(cert.verify(&constraints), Err(SosError::PositiveRhs));
}

#[test]
fn tamper_gram_not_psd_rejected() {
    let (constraints, mut cert) = linear_farkas_setup();
    // Force an indefinite Gram (adds a −x² to σ0 too, but PSD check fires first).
    cert.gram[1][1] = r(-1);
    assert_eq!(cert.verify(&constraints), Err(SosError::GramNotPsd));
}

#[test]
fn tamper_constraint_index_rejected() {
    let (constraints, mut cert) = linear_farkas_setup();
    cert.terms[0].origin = CertOrigin::Constraint(99);
    assert_eq!(cert.verify(&constraints), Err(SosError::BadConstraintIndex));
}

/// `{ x²+y² < 0 }` with the sum-of-squares refutation and `R = 0`.
#[test]
fn hand_sum_of_squares_zero_rhs_verifies() {
    let x = v(1);
    let y = v(2);
    // x²+y² < 0  →  poly = x²+y², Rel::Lt  ⇒ oriented g = −(x²+y²) > 0.
    let c0 = con(poly(&[(&[x, x], 1), (&[y, y], 1)]), Rel::Lt);
    let constraints = vec![c0];
    // σ0 = x²+y²  (Gram = diag(0,1,1) over [1,x,y]); + 1·g = 0.
    let cert = SosCertificate {
        basis: vec![vec![], vec![x], vec![y]],
        gram: vec![
            vec![r(0), r(0), r(0)],
            vec![r(0), r(1), r(0)],
            vec![r(0), r(0), r(1)],
        ],
        terms: vec![CertTerm {
            origin: CertOrigin::Constraint(0),
            multiplier: r(1),
        }],
        rhs: r(0),
    };
    assert_eq!(cert.verify(&constraints), Ok(()));
}

#[test]
fn zero_rhs_without_strict_term_rejected() {
    // Same SOS shape but the constraint is NONSTRICT (x²+y² ≤ 0). Then the
    // identity σ0 + 1·g = 0 holds, but with no strict term R = 0 proves nothing
    // (x²+y² = 0 IS feasible at the origin). The checker must reject.
    let x = v(1);
    let y = v(2);
    let c0 = con(poly(&[(&[x, x], 1), (&[y, y], 1)]), Rel::Le);
    let constraints = vec![c0];
    let cert = SosCertificate {
        basis: vec![vec![], vec![x], vec![y]],
        gram: vec![
            vec![r(0), r(0), r(0)],
            vec![r(0), r(1), r(0)],
            vec![r(0), r(0), r(1)],
        ],
        terms: vec![CertTerm {
            origin: CertOrigin::Constraint(0),
            multiplier: r(1),
        }],
        rhs: r(0),
    };
    assert_eq!(cert.verify(&constraints), Err(SosError::NonStrictZeroRhs));
}

// ---------------------------------------------------------------------------
// Search: trivial and hand instances.
// ---------------------------------------------------------------------------

#[test]
fn search_linear_farkas() {
    let x = v(1);
    let c0 = con(poly(&[(&[x], 1), (&[], -1)]), Rel::Ge); // x ≥ 1
    let c1 = con(poly(&[(&[x], 1)]), Rel::Le); // x ≤ 0
    let constraints = vec![c0, c1];
    let cert = search(&constraints, &[x]).expect("linear Farkas certificate");
    assert_eq!(cert.verify(&constraints), Ok(()));
    assert!(cert.rhs.is_negative());
}

#[test]
fn search_sum_of_squares_strict() {
    let x = v(1);
    let y = v(2);
    // x² + y² < 0.
    let c0 = con(poly(&[(&[x, x], 1), (&[y, y], 1)]), Rel::Lt);
    let constraints = vec![c0];
    let cert = search(&constraints, &[x, y]).expect("SOS certificate for x^2+y^2<0");
    assert_eq!(cert.verify(&constraints), Ok(()));
    // Strict-template certificate has R = 0.
    assert!(cert.rhs.is_zero());
}

#[test]
fn search_shifted_sum_of_squares() {
    // (x+y)^2 < 0. Oriented g = −(x+y)^2 > 0; σ0 = (x+y)^2 via the (x+y)^2
    // dictionary square.
    let x = v(1);
    let y = v(2);
    let c0 = con(poly(&[(&[x, x], 1), (&[x, y], 2), (&[y, y], 1)]), Rel::Lt);
    let constraints = vec![c0];
    let cert = search(&constraints, &[x, y]).expect("SOS certificate for (x+y)^2<0");
    assert_eq!(cert.verify(&constraints), Ok(()));
}

#[test]
fn search_gauge_style_box_pin_fit() {
    // A 2D pin-fit-style refutation, the shape the virtual-gauge clusters take:
    //   x² + y² ≥ 4   with   −1 ≤ x ≤ 1,  −1 ≤ y ≤ 1.
    // On the box the max of x²+y² is 2 < 4, so the system is UNSAT. The degree-2
    // Positivstellensatz uses the box PRODUCTS (1−x)(1+x) = 1−x² and
    // (1−y)(1+y) = 1−y² to cancel the +x², +y² of the lower bound:
    //   (x²+y²−4) + (1−x²) + (1−y²) = −2.
    let x = v(1);
    let y = v(2);
    let c0 = con(poly(&[(&[x, x], 1), (&[y, y], 1), (&[], -4)]), Rel::Ge); // x²+y² ≥ 4
    let c1 = con(poly(&[(&[x], 1), (&[], -1)]), Rel::Le); // x ≤ 1
    let c2 = con(poly(&[(&[x], 1), (&[], 1)]), Rel::Ge); // x ≥ −1
    let c3 = con(poly(&[(&[y], 1), (&[], -1)]), Rel::Le); // y ≤ 1
    let c4 = con(poly(&[(&[y], 1), (&[], 1)]), Rel::Ge); // y ≥ −1
    let constraints = vec![c0, c1, c2, c3, c4];
    let cert = search(&constraints, &[x, y]).expect("box-product Positivstellensatz certificate");
    assert_eq!(cert.verify(&constraints), Ok(()));
    assert!(cert.rhs.is_negative());
    // The certificate must actually use at least one product term.
    assert!(cert
        .terms
        .iter()
        .any(|t| matches!(t.origin, CertOrigin::Product(_, _))));
}

#[test]
fn search_equality_reduced_infeasibility() {
    // { y = 2, x²+y² ≤ 1 }  is UNSAT (y=2 ⇒ y²=4 > 1). Uses the equality
    // multiplier (free sign) plus box/SOS pieces:
    //   oriented: h = y − 2 (=0),  g = 1 − x² − y² (≥0).
    //   g + (x²) [σ0] + (y+2)·h = 1 − x² − y² + x² + (y²−4) = −3.
    // The (y+2)·h term needs a product of the equality with a linear form; the
    // search supports the base equality with a free constant multiplier, so the
    // reachable certificate is g + σ0(x²) + λ·h with λ a constant. Check the
    // search either finds a certificate or cleanly declines (never a bad cert).
    let x = v(1);
    let y = v(2);
    let ceq = con(poly(&[(&[y], 1), (&[], -2)]), Rel::Eq); // y = 2
    let cle = con(poly(&[(&[x, x], 1), (&[y, y], 1), (&[], -1)]), Rel::Le); // x²+y² ≤ 1
    let constraints = vec![ceq, cle];
    if let Some(cert) = search(&constraints, &[x, y]) {
        assert_eq!(cert.verify(&constraints), Ok(()));
    }
}

#[test]
fn search_declines_on_satisfiable_system() {
    // { x ≥ 0, x ≤ 1 } is SAT: there must be NO certificate.
    let x = v(1);
    let c0 = con(poly(&[(&[x], 1)]), Rel::Ge); // x ≥ 0
    let c1 = con(poly(&[(&[x], 1), (&[], -1)]), Rel::Le); // x ≤ 1
    assert!(search(&[c0, c1], &[x]).is_none());
}

#[test]
fn search_declines_on_satisfiable_circle() {
    // { x²+y² ≤ 4, x ≥ 0 } is SAT: no degree-2 refutation exists.
    let x = v(1);
    let y = v(2);
    let c0 = con(poly(&[(&[x, x], 1), (&[y, y], 1), (&[], -4)]), Rel::Le);
    let c1 = con(poly(&[(&[x], 1)]), Rel::Ge);
    assert!(search(&[c0, c1], &[x, y]).is_none());
}

// ---------------------------------------------------------------------------
// LP feasibility solver.
// ---------------------------------------------------------------------------

#[test]
fn lp_simple_feasible() {
    // x + y = 1, x, y ≥ 0. Feasible; recovered point satisfies the equation.
    let a = vec![vec![r(1), r(1)]];
    let b = vec![r(1)];
    let sol = lp_phase1_feasible(a, b, 2).expect("feasible");
    assert_eq!(&sol[0] + &sol[1], r(1));
    assert!(!sol[0].is_negative() && !sol[1].is_negative());
}

#[test]
fn lp_infeasible_negative_target() {
    // x = −1 with x ≥ 0 is infeasible.
    let a = vec![vec![r(1)]];
    let b = vec![r(-1)];
    assert!(lp_phase1_feasible(a, b, 1).is_none());
}

#[test]
fn lp_two_row_feasible() {
    // x + y + z = 2, x − y = 0, all ≥ 0.
    let a = vec![vec![r(1), r(1), r(1)], vec![r(1), r(-1), r(0)]];
    let b = vec![r(2), r(0)];
    let sol = lp_phase1_feasible(a, b, 3).expect("feasible");
    assert_eq!(&sol[0] + &sol[1] + &sol[2], r(2));
    assert_eq!(&sol[0] - &sol[1], r(0));
}

// ---------------------------------------------------------------------------
// Alethe rendering.
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// End-to-end: drive the real check() entry and confirm the certificate is
// produced and surfaced through the public accessors.
// ---------------------------------------------------------------------------

#[test]
fn end_to_end_sum_of_squares_unsat_carries_certificate() {
    use crate::NraSolver;
    use ay_core::term::TermStore;
    use ay_core::{Sort, TheoryResult, TheorySolver};

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let x2 = terms.mk_mul(vec![x, x]);
    let y2 = terms.mk_mul(vec![y, y]);
    let sum = terms.mk_add(vec![x2, y2]);
    let c0 = terms.mk_rational(r(0));
    let atom = terms.mk_lt(sum, c0); // x^2 + y^2 < 0

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(atom, true);
    let res = solver.check();
    assert!(matches!(res, TheoryResult::Unsat(_)), "x^2+y^2<0 is UNSAT");
    assert!(
        solver.took_sos_unsat_certificate(),
        "the UNSAT must carry an SOS certificate"
    );
    let rendered = solver
        .render_sos_unsat_certificate("t1")
        .expect("certificate renders");
    assert!(rendered.contains(":rule nra_positivstellensatz"));
}

#[test]
fn end_to_end_linear_farkas_unsat_carries_certificate() {
    use crate::NraSolver;
    use ay_core::term::TermStore;
    use ay_core::{Sort, TheoryResult, TheorySolver};

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let c1 = terms.mk_rational(r(1));
    let c0 = terms.mk_rational(r(0));
    let ge = terms.mk_ge(x, c1); // x >= 1
    let le = terms.mk_le(x, c0); // x <= 0

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(ge, true);
    solver.assert_literal(le, true);
    let res = solver.check();
    assert!(
        matches!(res, TheoryResult::Unsat(_)),
        "x>=1 & x<=0 is UNSAT"
    );
    assert!(
        solver.took_sos_unsat_certificate(),
        "the linear UNSAT must carry a Farkas (degree-0 SOS) certificate"
    );
}

#[test]
fn render_alethe_contains_rule_and_rhs() {
    let (constraints, cert) = linear_farkas_setup();
    assert_eq!(cert.verify(&constraints), Ok(()));
    let s = cert.render_alethe("t42", |t| format!("x{}", t.0));
    assert!(s.contains(":rule nra_positivstellensatz"));
    assert!(s.contains(":rhs -1"));
    assert!(s.contains("(cl)"));
    // A rational multiplier renders as (/ n d).
    assert!(render_rat(&rf(1, 2)) == "(/ 1 2)");
}
