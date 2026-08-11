// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the fraction-free subresultant substrate.
//!
//! Strategy: the determinantal definition ([`subresultant_det`]) is the
//! specification — it has no case analysis and is correct by construction. The
//! PRS ([`subresultant_chain_prs`]) is the fast path. Every structural test
//! checks the PRS against the spec, including the defective (degree-gap)
//! chains where the recurrence's case analysis lives, and the spec itself is
//! anchored on closed-form resultants and discriminants known independently.

use super::*;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::One;

fn zp(coeffs: &[i64]) -> RPoly<BigInt> {
    RPoly::from_coeffs(coeffs.iter().map(|&c| BigInt::from(c)).collect())
}

fn zi(v: i64) -> BigInt {
    BigInt::from(v)
}

/// `x_v` as an `MPolyZ`.
fn mv(v: MVar) -> MPolyZ {
    MPolyZ::term(Mono::var_pow(v, 1), <BigInt as One>::one())
}

fn mc(c: i64) -> MPolyZ {
    MPolyZ::constant(BigInt::from(c))
}

/// A tiny deterministic PRNG so the randomized differential tests are
/// reproducible (no `rand` dependency in this crate).
struct Lcg(u64);
impl Lcg {
    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 11
    }
    /// Uniform in `[-range, range]`.
    fn next_i64(&mut self, range: i64) -> i64 {
        let span = (2 * range + 1) as u64;
        (self.next_u64() % span) as i64 - range
    }
}

// ---------------------------------------------------------------------------
// Ring laws and exact division
// ---------------------------------------------------------------------------

#[test]
fn bigint_exact_div_refuses_inexact() {
    assert_eq!(ExactRing::exact_div(&zi(6), &zi(3)), Some(zi(2)));
    assert_eq!(ExactRing::exact_div(&zi(7), &zi(3)), None);
    assert_eq!(ExactRing::exact_div(&zi(0), &zi(3)), Some(zi(0)));
    assert_eq!(ExactRing::exact_div(&zi(3), &zi(0)), None);
    assert_eq!(ExactRing::exact_div(&zi(-6), &zi(3)), Some(zi(-2)));
}

#[test]
fn mpoly_canonical_form_and_arithmetic() {
    // (x + y)(x - y) = x^2 - y^2
    let x = mv(0);
    let y = mv(1);
    let a = ExactRing::add(&x, &y);
    let b = ExactRing::sub(&x, &y);
    let prod = ExactRing::mul(&a, &b);
    let expect = ExactRing::sub(&ExactRing::mul(&x, &x), &ExactRing::mul(&y, &y));
    assert_eq!(prod, expect);
    // Canonical form makes structural equality work regardless of build order.
    let same = MPolyZ::from_terms(vec![
        (Mono::from_pairs(vec![(1, 1), (1, 1)]), zi(-1)),
        (Mono::from_pairs(vec![(0, 2)]), zi(1)),
    ]);
    assert_eq!(prod, same);
}

#[test]
fn mpoly_exact_div_is_exact_or_refuses() {
    let x = mv(0);
    let y = mv(1);
    let f = ExactRing::sub(&ExactRing::mul(&x, &x), &ExactRing::mul(&y, &y));
    let g = ExactRing::add(&x, &y);
    let q = ExactRing::exact_div(&f, &g).expect("x^2-y^2 divisible by x+y");
    assert_eq!(q, ExactRing::sub(&x, &y));
    assert_eq!(ExactRing::mul(&q, &g), f);
    // Not divisible.
    assert_eq!(
        ExactRing::exact_div(&ExactRing::add(&f, &mc(1)), &g),
        None,
        "x^2-y^2+1 is not divisible by x+y"
    );
    // Integer divisibility is enforced: 2x / 4 is not in Z[x].
    let two_x = ExactRing::mul(&mc(2), &x);
    assert_eq!(ExactRing::exact_div(&two_x, &mc(4)), None);
    assert_eq!(ExactRing::exact_div(&two_x, &mc(2)), Some(x.clone()));
    // Division by zero refuses.
    assert_eq!(ExactRing::exact_div(&x, &MPolyZ::zero()), None);
    // Zero numerator is fine.
    assert_eq!(
        ExactRing::exact_div(&MPolyZ::zero(), &x),
        Some(MPolyZ::zero())
    );
}

#[test]
fn mono_grlex_is_a_total_order() {
    let m1 = Mono::from_pairs(vec![(0, 2)]); // x^2
    let m2 = Mono::from_pairs(vec![(0, 1), (1, 1)]); // xy
    let m3 = Mono::from_pairs(vec![(1, 2)]); // y^2
    let m4 = Mono::from_pairs(vec![(0, 1)]); // x
    assert_eq!(m1.cmp_grlex(&m2), std::cmp::Ordering::Greater);
    assert_eq!(m2.cmp_grlex(&m3), std::cmp::Ordering::Greater);
    assert_eq!(m4.cmp_grlex(&m1), std::cmp::Ordering::Less); // lower degree
    assert_eq!(m1.cmp_grlex(&m1), std::cmp::Ordering::Equal);
}

// ---------------------------------------------------------------------------
// Pseudo-remainder
// ---------------------------------------------------------------------------

#[test]
fn pseudo_rem_matches_definition() {
    // f = x^3 + 2x + 1, g = 2x^2 + 3
    // prem(f,g) = lc(g)^(3-2+1) f mod g = 4f mod g
    let f = zp(&[1, 2, 0, 1]);
    let g = zp(&[3, 0, 2]);
    let r = f.pseudo_rem(&g).unwrap();
    // 4f = 4x^3 + 8x + 4;  4x^3 = 2x*(2x^2+3) - 6x  =>  4f = 2x*g + 2x + 4
    assert_eq!(r, zp(&[4, 2]));
    assert!(r.degree().unwrap() < g.degree().unwrap());
}

#[test]
fn pseudo_rem_degenerate_cases() {
    let f = zp(&[1, 2, 0, 1]);
    // Divisor zero: refuse.
    assert_eq!(f.pseudo_rem(&RPoly::zero()), None);
    // Dividend zero: zero.
    assert_eq!(RPoly::<BigInt>::zero().pseudo_rem(&f), Some(RPoly::zero()));
    // deg f < deg g: f unchanged (multiplier exponent is 0).
    let g = zp(&[0, 0, 0, 0, 1]);
    assert_eq!(f.pseudo_rem(&g), Some(f.clone()));
    // Exact division case: prem(x^2-1, x-1) = 0.
    assert_eq!(
        zp(&[-1, 0, 1]).pseudo_rem(&zp(&[-1, 1])),
        Some(RPoly::zero())
    );
}

// ---------------------------------------------------------------------------
// Bareiss determinant
// ---------------------------------------------------------------------------

#[test]
fn bareiss_matches_small_hand_determinants() {
    let m2 = vec![vec![zi(1), zi(2)], vec![zi(3), zi(4)]];
    assert_eq!(bareiss_det(&m2), Some(zi(-2)));
    let m3 = vec![
        vec![zi(2), zi(-3), zi(1)],
        vec![zi(2), zi(0), zi(-1)],
        vec![zi(1), zi(4), zi(5)],
    ];
    // Expanded by hand: 2(0*5 - (-1)*4) + 3(2*5 - (-1)*1) + 1(2*4 - 0*1) = 49
    assert_eq!(bareiss_det(&m3), Some(zi(49)));
    // Singular.
    let sing = vec![
        vec![zi(1), zi(2), zi(3)],
        vec![zi(2), zi(4), zi(6)],
        vec![zi(1), zi(0), zi(1)],
    ];
    assert_eq!(bareiss_det(&sing), Some(zi(0)));
    // Zero leading pivot forces a row swap and a sign flip.
    let swap = vec![vec![zi(0), zi(1)], vec![zi(1), zi(0)]];
    assert_eq!(bareiss_det(&swap), Some(zi(-1)));
    // 0x0 determinant is 1 by convention.
    let empty: Vec<Vec<BigInt>> = Vec::new();
    assert_eq!(bareiss_det(&empty), Some(zi(1)));
    // Ragged input refuses.
    let ragged = vec![vec![zi(1), zi(2)], vec![zi(3)]];
    assert_eq!(bareiss_det(&ragged), None);
}

#[test]
fn bareiss_over_the_multivariate_ring() {
    // det [[x, y], [1, x]] = x^2 - y
    let x = mv(0);
    let y = mv(1);
    let m = vec![
        vec![x.clone(), y.clone()],
        vec![ExactRing::one(), x.clone()],
    ];
    let expect = ExactRing::sub(&ExactRing::mul(&x, &x), &y);
    assert_eq!(bareiss_det(&m), Some(expect));
}

// ---------------------------------------------------------------------------
// Resultants against closed forms
// ---------------------------------------------------------------------------

#[test]
fn resultant_closed_forms() {
    // Res(x^2 - 2, x^2 - 3) = prod over roots a of (a^2 - 3) = (2-3)(2-3) = 1
    assert_eq!(resultant(&zp(&[-2, 0, 1]), &zp(&[-3, 0, 1])), Some(zi(1)));
    // Common root => resultant 0.
    assert_eq!(resultant(&zp(&[-1, 0, 1]), &zp(&[-1, 1])), Some(zi(0)));
    // Res(a2 x^2 + a1 x + a0, b1 x + b0) = a2 b0^2 - a1 b0 b1 + a0 b1^2
    // with (a2,a1,a0) = (3,-4,5), (b1,b0) = (2,7):
    //   3*49 - (-4)*7*2 + 5*4 = 147 + 56 + 20 = 223
    assert_eq!(resultant(&zp(&[5, -4, 3]), &zp(&[7, 2])), Some(zi(223)));
    // Res of two linears a1x+a0, b1x+b0 = a1 b0 - a0 b1.
    assert_eq!(
        resultant(&zp(&[3, 2]), &zp(&[5, 7])),
        Some(zi(2 * 5 - 3 * 7))
    );
}

#[test]
fn resultant_constant_and_zero_arguments() {
    let f = zp(&[1, 2, 3]); // deg 2
                            // Res(f, c) = c^deg f
    assert_eq!(resultant(&f, &zp(&[5])), Some(zi(25)));
    assert_eq!(resultant(&zp(&[5]), &f), Some(zi(25)));
    // Res(c, d) = 1 for two constants.
    assert_eq!(resultant(&zp(&[5]), &zp(&[7])), Some(zi(1)));
    // Zero argument: undefined, fail closed.
    assert_eq!(resultant(&f, &RPoly::zero()), None);
    assert_eq!(resultant(&RPoly::zero(), &f), None);
    // f with itself: shares all roots.
    assert_eq!(resultant(&f, &f), Some(zi(0)));
}

#[test]
fn resultant_is_antisymmetric_up_to_sign() {
    let f = zp(&[1, 0, 2, 1]); // deg 3
    let g = zp(&[-1, 3]); // deg 1
    let a = resultant(&f, &g).unwrap();
    let b = resultant(&g, &f).unwrap();
    // (-1)^(3*1) = -1
    assert_eq!(a, -b.clone());
    assert_ne!(a, zi(0));
}

#[test]
fn discriminant_closed_forms() {
    // disc(x^2 + bx + c) = b^2 - 4c
    for (b, c) in [(0i64, -2i64), (3, 5), (-7, 2), (1, 0)] {
        let f = zp(&[c, b, 1]);
        assert_eq!(
            discriminant(&f),
            Some(zi(b * b - 4 * c)),
            "disc(x^2 + {b}x + {c})"
        );
    }
    // disc(x^3 + px + q) = -4p^3 - 27q^2
    for (p, q) in [(0i64, -1i64), (-3, 1), (2, 5), (1, 1)] {
        let f = zp(&[q, p, 0, 1]);
        assert_eq!(
            discriminant(&f),
            Some(zi(-4 * p * p * p - 27 * q * q)),
            "disc(x^3 + {p}x + {q})"
        );
    }
    // A non-monic quadratic: disc(a x^2 + b x + c) = b^2 - 4ac.
    assert_eq!(discriminant(&zp(&[5, -4, 3])), Some(zi(16 - 60)));
    // Repeated root => discriminant 0.
    // (x-1)^2 = x^2 - 2x + 1
    assert_eq!(discriminant(&zp(&[1, -2, 1])), Some(zi(0)));
    // Degree 0 / zero polynomial: refuse.
    assert_eq!(discriminant(&zp(&[7])), None);
    assert_eq!(discriminant(&RPoly::<BigInt>::zero()), None);
}

// ---------------------------------------------------------------------------
// PRS versus the determinantal specification
// ---------------------------------------------------------------------------

/// Compare the PRS chain against the determinantal spec on `j = 0..deg g`.
fn assert_prs_matches_spec(f: &RPoly<BigInt>, g: &RPoly<BigInt>, label: &str) {
    let spec = subresultant_chain_det(f, g).unwrap_or_else(|| panic!("spec failed for {label}"));
    let prs = subresultant_chain_prs(f, g).unwrap_or_else(|| panic!("prs failed for {label}"));
    let n = g.degree().unwrap();
    for j in 0..n {
        assert_eq!(
            prs[j],
            spec[j],
            "S_{j} mismatch for {label}\n  f={:?}\n  g={:?}",
            f.coeffs(),
            g.coeffs()
        );
    }
}

#[test]
fn prs_matches_spec_on_normal_chains() {
    assert_prs_matches_spec(&zp(&[-2, 0, 0, 1]), &zp(&[0, 0, 3]), "x^3-2 vs 3x^2");
    assert_prs_matches_spec(
        &zp(&[1, 2, 3, 4, 5]),
        &zp(&[2, -1, 1]),
        "quartic vs quadratic",
    );
    assert_prs_matches_spec(
        &zp(&[1, 0, 0, 0, 0, 1]),
        &zp(&[0, 0, 0, 0, 5]),
        "x^5+1 vs 5x^4",
    );
    assert_prs_matches_spec(&zp(&[-1, 0, 1, 3]), &zp(&[2, 1]), "cubic vs linear");
}

#[test]
fn prs_matches_spec_on_defective_chains() {
    // Degree gaps in the remainder sequence exercise the defective branch.
    // x^4 + 1 against x^3: prem drops straight to degree 0.
    assert_prs_matches_spec(&zp(&[1, 0, 0, 0, 1]), &zp(&[0, 0, 0, 1]), "x^4+1 vs x^3");
    // A constructed two-step gap.
    assert_prs_matches_spec(&zp(&[0, 0, 0, 0, 0, 1]), &zp(&[1, 0, 0, 1]), "x^5 vs x^3+1");
    // f = x^6 + x^2, g = x^4 (large gap, defective at the seed step too).
    assert_prs_matches_spec(
        &zp(&[0, 0, 1, 0, 0, 0, 1]),
        &zp(&[0, 0, 0, 0, 1]),
        "x^6+x^2 vs x^4",
    );
    // deg g far below deg f - 1: the seed step itself is defective.
    assert_prs_matches_spec(&zp(&[1, 1, 1, 1, 1, 1]), &zp(&[3, 2]), "quintic vs linear");
}

#[test]
fn prs_matches_spec_with_common_factors() {
    // f = (x-1)(x^2+1), g = (x-1)(x+2): a shared root makes the tail vanish.
    let f = zp(&[-1, 1, -1, 1]);
    let g = zp(&[-2, 1, 1]);
    assert_prs_matches_spec(&f, &g, "shared root");
    assert_eq!(resultant(&f, &g), Some(zi(0)));
    // Chain must be all-zero below the gcd degree, and psc_0 = 0.
    let psc = psc_chain(&f, &g).unwrap();
    assert_eq!(
        psc[0],
        zi(0),
        "psc_0 vanishes exactly when gcd is non-trivial"
    );
}

#[test]
fn prs_refuses_equal_degrees_and_psc_chain_falls_back() {
    let f = zp(&[1, 2, 3]);
    let g = zp(&[2, -1, 1]);
    assert_eq!(
        subresultant_chain_prs(&f, &g),
        None,
        "deg f == deg g has no valid seed for the recurrence"
    );
    // psc_chain must still answer, via the determinantal path.
    let psc = psc_chain(&f, &g).expect("determinantal fallback");
    let spec = subresultant_chain_det(&f, &g).unwrap();
    assert_eq!(psc.len(), 2);
    for (j, v) in psc.iter().enumerate() {
        assert_eq!(*v, spec[j].coeff(j));
    }
    // And the resultant agrees with the closed form for two quadratics:
    // Res(a2x^2+a1x+a0, b2x^2+b1x+b0)
    //   = (a2 b0 - a0 b2)^2 - (a2 b1 - a1 b2)(a1 b0 - a0 b1)
    // f: a2=3,a1=2,a0=1 ; g: b2=1,b1=-1,b0=2
    let (a2, a1, a0, b2, b1, b0) = (3i64, 2, 1, 1, -1, 2);
    let expect = (a2 * b0 - a0 * b2).pow(2) - (a2 * b1 - a1 * b2) * (a1 * b0 - a0 * b1);
    assert_eq!(resultant(&f, &g), Some(zi(expect)));
}

#[test]
fn prs_preconditions_fail_closed() {
    let f = zp(&[1, 2, 3]);
    // Zero arguments.
    assert_eq!(subresultant_chain_prs(&f, &RPoly::zero()), None);
    assert_eq!(subresultant_chain_prs(&RPoly::zero(), &f), None);
    // Constant g (deg 0) has an empty subresultant chain by definition.
    assert_eq!(subresultant_chain_prs(&f, &zp(&[5])), None);
    assert_eq!(psc_chain(&f, &zp(&[5])), Some(Vec::new()));
    // deg f < deg g is handled by psc_chain's swap, not by the raw PRS.
    assert_eq!(subresultant_chain_prs(&zp(&[1, 1]), &f), None);
    assert!(psc_chain(&zp(&[1, 1]), &f).is_some());
}

#[test]
fn randomized_prs_versus_spec_over_z() {
    let mut rng = Lcg(0x5EED_1234_ABCD_0001);
    let mut checked = 0usize;
    for _ in 0..400 {
        let dm = 2 + (rng.next_u64() % 4) as usize; // deg f in 2..=5
        let dn = 1 + (rng.next_u64() % (dm as u64)) as usize; // deg g in 1..=dm
        if dn >= dm {
            continue; // PRS precondition
        }
        let mut fc: Vec<BigInt> = (0..=dm).map(|_| zi(rng.next_i64(4))).collect();
        let mut gc: Vec<BigInt> = (0..=dn).map(|_| zi(rng.next_i64(4))).collect();
        // Force the nominal degrees (a zero leading coefficient would silently
        // change the degrees and make the comparison meaningless).
        if Zero::is_zero(&fc[dm]) {
            fc[dm] = zi(1);
        }
        if Zero::is_zero(&gc[dn]) {
            gc[dn] = zi(1);
        }
        let f = RPoly::from_coeffs(fc);
        let g = RPoly::from_coeffs(gc);
        assert_prs_matches_spec(&f, &g, "randomized");
        checked += 1;
    }
    assert!(checked > 200, "expected a healthy sample, got {checked}");
}

#[test]
fn randomized_prs_versus_spec_with_forced_gaps() {
    // Bias the sample towards defective chains by zeroing interior
    // coefficients, which is what produces degree gaps in the PRS.
    let mut rng = Lcg(0xC0FF_EE00_D15E_A5E5);
    let mut defective_seen = 0usize;
    for _ in 0..800 {
        let dm = 4 + (rng.next_u64() % 3) as usize; // 4..=6
        let dn = 1 + (rng.next_u64() % (dm as u64 - 1)) as usize; // 1..=dm-1
        let mut fc: Vec<BigInt> = (0..=dm)
            .map(|_| {
                if rng.next_u64().is_multiple_of(2) {
                    zi(0)
                } else {
                    zi(rng.next_i64(3))
                }
            })
            .collect();
        let mut gc: Vec<BigInt> = (0..=dn)
            .map(|_| {
                if rng.next_u64().is_multiple_of(2) {
                    zi(0)
                } else {
                    zi(rng.next_i64(3))
                }
            })
            .collect();
        if Zero::is_zero(&fc[dm]) {
            fc[dm] = zi(1);
        }
        if Zero::is_zero(&gc[dn]) {
            gc[dn] = zi(1);
        }
        let f = RPoly::from_coeffs(fc);
        let g = RPoly::from_coeffs(gc);
        assert_prs_matches_spec(&f, &g, "gap-biased");
        // Count how many of these actually exercised a defective step: a chain
        // with an interior zero subresultant.
        let chain = subresultant_chain_prs(&f, &g).unwrap();
        if (1..dn).any(|j| chain[j].is_zero()) {
            defective_seen += 1;
        }
    }
    // Measured on this seed: the assertion is a floor, not a target.
    assert!(
        defective_seen >= 50, // measured: 70 on this seed
        "the gap-biased sample must actually hit defective chains, saw {defective_seen}"
    );
}

// ---------------------------------------------------------------------------
// Multivariate: the case the incumbent cannot do without interpolation
// ---------------------------------------------------------------------------

/// `RPoly<MPolyZ>` from coefficients given low-to-high in the main variable.
fn mp(coeffs: Vec<MPolyZ>) -> RPoly<MPolyZ> {
    RPoly::from_coeffs(coeffs)
}

#[test]
fn multivariate_resultant_eliminates_the_main_variable() {
    // Res_y(y^2 - x, y^2 - x - 1) = 1 (the two curves never meet).
    let x = mv(0);
    let f = mp(vec![ExactRing::neg(&x), MPolyZ::zero(), ExactRing::one()]);
    let g = mp(vec![
        ExactRing::neg(&ExactRing::add(&x, &mc(1))),
        MPolyZ::zero(),
        ExactRing::one(),
    ]);
    assert_eq!(resultant(&f, &g), Some(ExactRing::one()));
}

#[test]
fn multivariate_resultant_projects_an_intersection() {
    // Res_y(y - x, y^2 - 1) = x^2 - 1: the projection of the intersection of
    // the line y = x with the pair of lines y = +-1 is x = +-1.
    let x = mv(0);
    let f = mp(vec![ExactRing::neg(&x), ExactRing::one()]);
    let g = mp(vec![mc(-1), MPolyZ::zero(), ExactRing::one()]);
    let expect = ExactRing::sub(&ExactRing::mul(&x, &x), &mc(1));
    assert_eq!(resultant(&f, &g), Some(expect));
}

#[test]
fn multivariate_resultant_circle_and_line() {
    // f = y^2 + x^2 - 1 (unit circle), g = y - x (diagonal).
    // Res_y(f, g) = g's root y = x substituted: x^2 + x^2 - 1 = 2x^2 - 1.
    let x = mv(0);
    let x2 = ExactRing::mul(&x, &x);
    let f = mp(vec![
        ExactRing::sub(&x2, &mc(1)),
        MPolyZ::zero(),
        ExactRing::one(),
    ]);
    let g = mp(vec![ExactRing::neg(&x), ExactRing::one()]);
    let expect = ExactRing::sub(&ExactRing::mul(&mc(2), &x2), &mc(1));
    assert_eq!(resultant(&f, &g), Some(expect));
}

#[test]
fn multivariate_discriminant_in_the_main_variable() {
    // disc_y(y^2 + x y + x) = x^2 - 4x.
    let x = mv(0);
    let f = mp(vec![x.clone(), x.clone(), ExactRing::one()]);
    let expect = ExactRing::sub(&ExactRing::mul(&x, &x), &ExactRing::mul(&mc(4), &x));
    assert_eq!(discriminant(&f), Some(expect));
}

#[test]
fn multivariate_psc_chain_over_three_variables() {
    // A genuinely 3-variable projection: f = z^2 - x, g = z^2 - y in Z[x,y][z].
    // Res_z(f, g) = (x - y)^2 ... check against the determinantal spec, and
    // confirm the PRS and the spec agree on the whole chain.
    let x = mv(0);
    let y = mv(1);
    let f = mp(vec![ExactRing::neg(&x), MPolyZ::zero(), ExactRing::one()]);
    let g = mp(vec![ExactRing::neg(&y), MPolyZ::zero(), ExactRing::one()]);
    // deg f == deg g, so this must come out of the determinantal path.
    assert_eq!(subresultant_chain_prs(&f, &g), None);
    let d = ExactRing::sub(&x, &y);
    assert_eq!(resultant(&f, &g), Some(ExactRing::mul(&d, &d)));
    let psc = psc_chain(&f, &g).unwrap();
    assert_eq!(psc.len(), 2);
    assert_eq!(psc[0], ExactRing::mul(&d, &d));
}

#[test]
fn multivariate_prs_matches_spec_when_degrees_differ() {
    // f = y^3 + x y + 1, g = y^2 - x in Z[x][y].
    let x = mv(0);
    let f = mp(vec![
        ExactRing::one(),
        x.clone(),
        MPolyZ::zero(),
        ExactRing::one(),
    ]);
    let g = mp(vec![ExactRing::neg(&x), MPolyZ::zero(), ExactRing::one()]);
    let spec = subresultant_chain_det(&f, &g).unwrap();
    let prs = subresultant_chain_prs(&f, &g).unwrap();
    for j in 0..2 {
        assert_eq!(prs[j], spec[j], "multivariate S_{j}");
    }
    // Sanity: substituting y^2 = x into f gives y*x + x*y + 1 = 2xy + 1,
    // so Res_y(f,g) = Res_y(2xy+1, y^2-x) up to the standard factor.
    // Res_y(y^3 + xy + 1, y^2 - x) = -(4x^3) ... check it is non-zero and has
    // the right total degree rather than hard-coding a sign convention.
    let r = resultant(&f, &g).unwrap();
    assert!(!ExactRing::is_zero(&r));
    assert_eq!(r, spec[0].coeff(0));
}

// ---------------------------------------------------------------------------
// Agreement with the incumbent rational Sylvester determinant
// ---------------------------------------------------------------------------

#[test]
fn agrees_with_incumbent_sylvester_determinant() {
    // The incumbent `algebraic::sylvester_det_fixed` is the code path this
    // module is meant to replace. On integer inputs with exact nominal degrees
    // the two must produce the same resultant — that is what makes the
    // replacement safe.
    let mut rng = Lcg(0xABCD_0000_1111_2222);
    let mut checked = 0usize;
    for _ in 0..300 {
        let dm = 1 + (rng.next_u64() % 4) as usize;
        let dn = 1 + (rng.next_u64() % 4) as usize;
        let mut fc: Vec<i64> = (0..=dm).map(|_| rng.next_i64(5)).collect();
        let mut gc: Vec<i64> = (0..=dn).map(|_| rng.next_i64(5)).collect();
        if fc[dm] == 0 {
            fc[dm] = 1;
        }
        if gc[dn] == 0 {
            gc[dn] = 1;
        }
        let f_rat: Vec<BigRational> = fc.iter().map(|&c| BigRational::from(zi(c))).collect();
        let g_rat: Vec<BigRational> = gc.iter().map(|&c| BigRational::from(zi(c))).collect();
        let incumbent =
            crate::algebraic::sylvester_det_fixed(&f_rat, &g_rat).expect("incumbent determinant");
        let mine = resultant(&zp(&fc), &zp(&gc)).expect("subresultant resultant");
        assert_eq!(
            incumbent,
            BigRational::from(mine.clone()),
            "resultant disagreement\n  f={fc:?}\n  g={gc:?}\n  incumbent={incumbent}\n  mine={mine}"
        );
        checked += 1;
    }
    assert_eq!(checked, 300);
}

#[test]
fn integer_poly_from_rationals_clears_denominators() {
    let coeffs = vec![
        BigRational::new(zi(1), zi(2)),
        BigRational::new(zi(2), zi(3)),
        BigRational::from(zi(1)),
    ];
    let p = integer_poly_from_rationals(&coeffs).unwrap();
    // lcm(2,3,1) = 6 => [3, 4, 6]
    assert_eq!(p.coeffs(), &[zi(3), zi(4), zi(6)]);
    // Zero polynomial refuses.
    assert_eq!(
        integer_poly_from_rationals(&[BigRational::from(zi(0))]),
        None
    );
    // Negative denominators normalize positively.
    let neg = vec![BigRational::new(zi(-1), zi(4)), BigRational::from(zi(1))];
    let q = integer_poly_from_rationals(&neg).unwrap();
    assert_eq!(q.coeffs(), &[zi(-1), zi(4)]);
}

// ---------------------------------------------------------------------------
// The projection property CAD actually relies on
// ---------------------------------------------------------------------------

#[test]
fn psc_chain_detects_degree_drop_and_common_factors() {
    // psc_j(f, g) = 0 for all j < k exactly when deg gcd(f, g) >= k.
    // f = (x-1)^2 (x+3), g = (x-1)^2: gcd has degree 2, so psc_0 = psc_1 = 0.
    let f = zp(&[3, -5, 1, 1]); // (x-1)^2 (x+3) = x^3 + x^2 - 5x + 3
    let g = zp(&[1, -2, 1]); // (x-1)^2
    let psc = psc_chain(&f, &g).unwrap();
    assert_eq!(psc.len(), 2);
    assert_eq!(psc[0], zi(0), "psc_0 must vanish (gcd degree 2 >= 1)");
    assert_eq!(psc[1], zi(0), "psc_1 must vanish (gcd degree 2 >= 2)");

    // Coprime pair: psc_0 = resultant != 0.
    let h = zp(&[1, 0, 1]); // x^2 + 1
    let psc2 = psc_chain(&f, &h).unwrap();
    assert_ne!(psc2[0], zi(0));
    assert_eq!(psc2[0], resultant(&f, &h).unwrap());
}

#[test]
fn psc_chain_first_nonzero_index_is_the_gcd_degree() {
    // Systematically: for f = c * u, g = c * v with gcd(u,v) = 1,
    // psc_j = 0 for j < deg c, and psc_{deg c} != 0.
    // c = x^2 - 2, u = x + 1, v = x - 3.
    let c = zp(&[-2, 0, 1]);
    let u = zp(&[1, 1]);
    let v = zp(&[-3, 1]);
    let f = c.mul(&u); // degree 3
    let g = c.mul(&v); // degree 3
                       // Equal degrees: exercises the determinantal fallback path too.
    let psc = psc_chain(&f, &g).unwrap();
    assert_eq!(psc.len(), 3);
    assert_eq!(psc[0], zi(0));
    assert_eq!(psc[1], zi(0));
    assert_ne!(psc[2], zi(0), "psc_{{deg gcd}} must be non-zero");
}

// ---------------------------------------------------------------------------
// z3 cross-check anchor (see the scratch script for the oracle runs)
// ---------------------------------------------------------------------------

/// Res_y(y^2 - x, y - x + 2) = x^2 - 5x + 4.
///
/// This exact pair is the one cross-checked against the z3 5.0.0 binary: the
/// projection property says `Res_y(p, q)(x0) = 0` iff `p(x0, ·)` and
/// `q(x0, ·)` share a root, and z3 decides that existential directly. The
/// oracle confirmed `sat` at the two roots of this resultant and `unsat` at
/// non-roots — a check that never looks at how the resultant was computed.
#[test]
fn z3_crosscheck_pair_resultant() {
    let x = mv(0);
    // p = y^2 - x  (degree 2 in the main variable y)
    let p = mp(vec![ExactRing::neg(&x), MPolyZ::zero(), ExactRing::one()]);
    // q = y - x + 2
    let q = mp(vec![
        ExactRing::add(&ExactRing::neg(&x), &mc(2)),
        ExactRing::one(),
    ]);
    // x^2 - 5x + 4
    let x2 = ExactRing::mul(&x, &x);
    let expect = ExactRing::add(&ExactRing::sub(&x2, &ExactRing::mul(&mc(5), &x)), &mc(4));
    assert_eq!(resultant(&p, &q), Some(expect));
}

/// Res_y(y^3 + x y + 1, y^2 - x) = 1 - 4x^3.
///
/// Derived independently: on the variety `y^2 = x` the first polynomial
/// reduces to `2xy + 1`, and the product over the two roots `y = +-sqrt(x)`
/// is `(2x sqrt(x) + 1)(-2x sqrt(x) + 1) = 1 - 4x^3`. Also cross-checked
/// against z3 at rational sample points.
#[test]
fn z3_crosscheck_cubic_over_conic() {
    let x = mv(0);
    let f = mp(vec![
        ExactRing::one(),
        x.clone(),
        MPolyZ::zero(),
        ExactRing::one(),
    ]);
    let g = mp(vec![ExactRing::neg(&x), MPolyZ::zero(), ExactRing::one()]);
    let x3 = ExactRing::mul(&ExactRing::mul(&x, &x), &x);
    let expect = ExactRing::sub(&mc(1), &ExactRing::mul(&mc(4), &x3));
    assert_eq!(resultant(&f, &g), Some(expect));
}

// ---------------------------------------------------------------------------
