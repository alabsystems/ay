// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for [`crate::anum`].
//!
//! These are the *cheap* half of the coverage: the differential oracle
//! (`crates/ay-nra-oracle`, checks `anum-*`) is where the real coverage lives,
//! because it compares against z3 rather than against this file's expectations.

use super::*;

fn zp(c: &[i64]) -> ZPoly {
    ZPoly::from_coeffs(c.iter().map(|&v| BigInt::from(v)).collect())
}

fn iv(lo: i64, hi: i64) -> BqInterval {
    BqInterval::new(
        Bq::from_int(BigInt::from(lo)),
        Bq::from_int(BigInt::from(hi)),
    )
    .unwrap()
}

fn ivk(lo: i64, hi: i64, k: u32) -> BqInterval {
    BqInterval::new(Bq::new(BigInt::from(lo), k), Bq::new(BigInt::from(hi), k)).unwrap()
}

/// `sqrt(2)`: the positive root of `x^2 - 2`, isolated by `(1, 2)`.
fn sqrt2() -> Anum {
    Anum::from_poly_interval(
        &[BigInt::from(-2), BigInt::zero(), BigInt::one()],
        &iv(1, 2),
    )
    .unwrap()
}

/// `-sqrt(2)`.
fn neg_sqrt2() -> Anum {
    Anum::from_poly_interval(
        &[BigInt::from(-2), BigInt::zero(), BigInt::one()],
        &iv(-2, -1),
    )
    .unwrap()
}

#[test]
fn sturm_chain_counts_roots_of_a_cubic() {
    // (x-1)(x-2)(x-3) = x^3 - 6x^2 + 11x - 6
    let p = zp(&[-6, 11, -6, 1]);
    let chain = sturm_chain(&p).unwrap();
    assert_eq!(
        sturm_count_in(
            &chain,
            &Bq::from_int(BigInt::from(0)),
            &Bq::from_int(BigInt::from(10))
        ),
        Some(3)
    );
    // (0, 3/2) contains only the root at 1.
    assert_eq!(
        sturm_count_in(
            &chain,
            &Bq::from_int(BigInt::from(0)),
            &Bq::new(BigInt::from(3), 1)
        ),
        Some(1)
    );
    // Endpoint on a root: refused, not silently off by one.
    assert_eq!(
        sturm_count_in(
            &chain,
            &Bq::from_int(BigInt::from(1)),
            &Bq::from_int(BigInt::from(10))
        ),
        None
    );
}

#[test]
fn constructor_refuses_a_non_isolating_interval() {
    let p = [BigInt::from(-2), BigInt::zero(), BigInt::one()];
    // (-2, 2) contains BOTH roots of x^2 - 2.
    assert!(Anum::from_poly_interval(&p, &iv(-2, 2)).is_none());
    // (1, 2) contains exactly one.
    assert!(Anum::from_poly_interval(&p, &iv(1, 2)).is_some());
    // (3, 4) contains none.
    assert!(Anum::from_poly_interval(&p, &iv(3, 4)).is_none());
}

#[test]
fn constructor_refuses_a_root_endpoint() {
    // x^2 - 1 has roots -1 and 1; (1, 3) has a root ON the lower endpoint.
    let p = [BigInt::from(-1), BigInt::zero(), BigInt::one()];
    assert!(Anum::from_poly_interval(&p, &iv(1, 3)).is_none());
    assert!(Anum::from_poly_interval(&p, &iv(0, 3)).is_some());
}

#[test]
fn a_linear_defining_polynomial_collapses_to_a_rational() {
    // 3x - 1 -> 1/3, which is NOT dyadic.
    let a = Anum::from_poly_interval(&[BigInt::from(-1), BigInt::from(3)], &iv(0, 1)).unwrap();
    assert!(a.is_rational());
    assert_eq!(
        a.to_rational().unwrap(),
        &BigRational::new(BigInt::one(), BigInt::from(3))
    );
}

#[test]
fn normalization_strips_multiplicity_and_content() {
    // 4*(x^2 - 2)^2: content 4, multiplicity 2. Radical is x^2 - 2.
    let sq = zp(&[-2, 0, 1]);
    let p = sq.mul(&sq).scale(&BigInt::from(4));
    let n = normalize_defining(&p).unwrap();
    assert_eq!(n, sq);
}

#[test]
fn root_index_is_derived_not_stored() {
    // x^3 - 6x^2 + 11x - 6 has roots 1 < 2 < 3.
    let p: Vec<BigInt> = [-6i64, 11, -6, 1]
        .iter()
        .map(|&v| BigInt::from(v))
        .collect();
    for (lo, hi, want) in [(0i64, 3i64, 1usize), (3, 5, 2), (5, 7, 3)] {
        // Halve the integer endpoints so they miss the roots at 1, 2, 3.
        let a = Anum::from_poly_interval(&p, &ivk(lo, hi, 1)).unwrap();
        assert_eq!(
            a.cell().unwrap().root_index(),
            Some(want),
            "({lo}/2, {hi}/2)"
        );
    }
}

#[test]
fn separation_exponent_is_a_valid_lower_bound() {
    // x^3 - 6x^2 + 11x - 6: roots 1, 2, 3, minimum gap 1 = 2^0.
    let p = zp(&[-6, 11, -6, 1]);
    let b = root_separation_exponent(&p).unwrap();
    // 2^-b must be strictly below the true gap of 1.
    assert!(b >= 1, "bound 2^-{b} must be < 1");
    // Degree < 2: vacuous.
    assert_eq!(root_separation_exponent(&zp(&[-1, 2])), Some(0));
}

#[test]
fn compare_sqrt2_against_rationals_exactly() {
    let a = sqrt2();
    let r = |n: i64, d: i64| BigRational::new(BigInt::from(n), BigInt::from(d));
    assert_eq!(
        a.cmp_anum(&Anum::rational(r(14142135, 10000000))),
        Some(Ordering::Greater)
    );
    assert_eq!(
        a.cmp_anum(&Anum::rational(r(14142136, 10000000))),
        Some(Ordering::Less)
    );
    assert_eq!(a.cmp_anum(&neg_sqrt2()), Some(Ordering::Greater));
}

#[test]
fn equal_algebraic_numbers_compare_equal_with_zero_refinement() {
    // The same root reached through two DIFFERENT defining polynomials:
    // x^2 - 2 and (x^2 - 2)(x^2 - 3) — the second is not minimal.
    let a = sqrt2();
    // (1, 3/2) brackets sqrt(2) ~ 1.4142 and excludes sqrt(3) ~ 1.7320.
    let big = zp(&[-2, 0, 1]).mul(&zp(&[-3, 0, 1]));
    let b = Anum::from_poly_interval(big.coeffs(), &ivk(2, 3, 1)).unwrap();
    let (ord, trace) = a.cmp_anum_traced(&b).unwrap();
    assert_eq!(ord, Ordering::Equal);
    assert!(trace.equal_by_certificate, "equality must be certified");
    assert_eq!(
        (trace.steps_a, trace.steps_b),
        (0, 0),
        "no bisection allowed"
    );
}

#[test]
fn sign_of_a_polynomial_vanishing_at_the_point_is_exactly_zero() {
    let a = sqrt2();
    // x^2 - 2 vanishes at sqrt(2).
    assert_eq!(
        a.sign_of_poly(&[BigInt::from(-2), BigInt::zero(), BigInt::one()]),
        Some(0)
    );
    // x^4 - 4 also vanishes there (it is (x^2-2)(x^2+2)).
    let q: Vec<BigInt> = [-4i64, 0, 0, 0, 1]
        .iter()
        .map(|&v| BigInt::from(v))
        .collect();
    assert_eq!(a.sign_of_poly(&q), Some(0));
    // x - 1 is positive at sqrt(2); x - 2 is negative.
    assert_eq!(a.sign_of_poly(&[BigInt::from(-1), BigInt::one()]), Some(1));
    assert_eq!(a.sign_of_poly(&[BigInt::from(-2), BigInt::one()]), Some(-1));
}

/// Documents the DEFERRED piece precisely: without factorization over `Z` the
/// result of an arithmetic op keeps a reducible square-free defining polynomial
/// (`z^3 - 8z` here, not `z`), so it does **not** collapse to the rational case
/// — but it is still exactly zero, and `cmp_anum` says so through the gcd
/// certificate. Soundness does not depend on minimality; canonicity does.
#[test]
fn sum_of_sqrt2_and_negative_sqrt2_is_exactly_zero() {
    let s = sqrt2().add(&neg_sqrt2()).unwrap();
    assert!(
        !s.is_rational(),
        "documented deferral: no factorization over Z"
    );
    assert_eq!(s.cell().unwrap().poly_coeffs().len(), 4, "z^3 - 8z");
    assert_eq!(
        s.cmp_anum(&Anum::rational(BigRational::zero())),
        Some(Ordering::Equal)
    );
    assert_eq!(s.sign_of_poly(&[BigInt::zero(), BigInt::one()]), Some(0));
}

#[test]
fn product_of_sqrt2_with_itself_is_exactly_two() {
    let s = sqrt2().mul(&sqrt2()).unwrap();
    assert_eq!(
        s.cmp_anum(&Anum::rational(BigRational::from_integer(BigInt::from(2)))),
        Some(Ordering::Equal)
    );
    // And strictly between 1 and 3, which pins the branch of `z^2 - 4` chosen.
    assert_eq!(
        s.cmp_anum(&Anum::rational(BigRational::from_integer(BigInt::from(1)))),
        Some(Ordering::Greater)
    );
    assert_eq!(
        s.cmp_anum(&Anum::rational(BigRational::from_integer(BigInt::from(3)))),
        Some(Ordering::Less)
    );
}

#[test]
fn product_of_sqrt2_and_negative_sqrt2_is_exactly_minus_two() {
    let s = sqrt2().mul(&neg_sqrt2()).unwrap();
    assert_eq!(
        s.cmp_anum(&Anum::rational(BigRational::from_integer(BigInt::from(-2)))),
        Some(Ordering::Equal)
    );
}

#[test]
fn multiplying_by_a_rational_goes_through_the_same_resultant_path() {
    let half = Anum::rational(BigRational::new(BigInt::one(), BigInt::from(2)));
    let s = sqrt2().mul(&half).unwrap();
    // (sqrt(2)/2)^2 == 1/2, i.e. 2x^2 - 1 vanishes there.
    assert_eq!(
        s.sign_of_poly(&[BigInt::from(-1), BigInt::zero(), BigInt::from(2)]),
        Some(0)
    );
    assert_eq!(s.cmp_anum(&sqrt2()), Some(Ordering::Less));
    let t = sqrt2().add(&half).unwrap();
    assert_eq!(t.cmp_anum(&sqrt2()), Some(Ordering::Greater));
}

#[test]
fn sqrt2_plus_sqrt3_satisfies_its_minimal_polynomial() {
    let a = sqrt2();
    let b = Anum::from_poly_interval(
        &[BigInt::from(-3), BigInt::zero(), BigInt::one()],
        &iv(1, 2),
    )
    .unwrap();
    let s = a.add(&b).unwrap();
    // x^4 - 10x^2 + 1 is the minimal polynomial of sqrt(2) + sqrt(3).
    let m: Vec<BigInt> = [1i64, 0, -10, 0, 1]
        .iter()
        .map(|&v| BigInt::from(v))
        .collect();
    assert_eq!(s.sign_of_poly(&m), Some(0));
    // And it is strictly between 3 and 4.
    assert_eq!(
        s.cmp_anum(&Anum::rational(BigRational::from_integer(BigInt::from(3)))),
        Some(Ordering::Greater)
    );
    assert_eq!(
        s.cmp_anum(&Anum::rational(BigRational::from_integer(BigInt::from(4)))),
        Some(Ordering::Less)
    );
}

#[test]
fn refinement_preserves_the_invariant_and_narrows() {
    let a = sqrt2();
    let target = Bq::inv_two_pow(20);
    let r = a.refine(&target).unwrap();
    let c = r.cell().unwrap();
    assert!(c.interval().width().cmp_bq(&target) != Ordering::Greater);
    // Still the same number.
    assert_eq!(a.cmp_anum(&r), Some(Ordering::Equal));
    // Still isolating: re-running the constructor on the narrowed data accepts.
    assert!(Anum::from_poly_interval(c.poly_coeffs(), c.interval()).is_some());
}

#[test]
fn negation_reflects_the_interval() {
    let n = sqrt2().neg().unwrap();
    assert_eq!(n.cmp_anum(&neg_sqrt2()), Some(Ordering::Equal));
}

// ============================================================================
// The escalation ladder and the coprime separation shortcut
// ============================================================================

/// A small corpus of genuinely algebraic numbers, built the way callers do.
fn ladder_corpus() -> Vec<Anum> {
    let mut out = Vec::new();
    for d in [2i64, 3, 5, 6, 7, 10, 11, 13] {
        // The positive root of `x^2 - d`.
        if let Some(a) = Anum::from_poly_interval(
            &[BigInt::from(-d), BigInt::zero(), BigInt::one()],
            &iv(0, d + 1),
        ) {
            out.push(a);
        }
    }
    for (n, d) in [(3usize, 2i64), (3, 5), (4, 2), (4, 7), (5, 3), (6, 2)] {
        let mut c = vec![BigInt::zero(); n + 1];
        c[0] = BigInt::from(-d);
        c[n] = BigInt::one();
        if let Some(a) = Anum::from_poly_interval(&c, &iv(0, d + 1)) {
            out.push(a);
        }
    }
    out
}

/// THE soundness property the coprime shortcut in `separation_exponent_for_pair`
/// rests on: skipping the square-free radical of the product may only make the
/// derived exponent LARGER — a weaker but still valid separation bound — never
/// smaller.
///
/// A smaller exponent would be an unsound bound, and an unsound bound is how a
/// comparison silently returns the wrong order. This is the one direction that
/// must never regress, so it is asserted directly rather than left to the
/// differential oracle to notice.
#[test]
fn the_coprime_separation_shortcut_never_understates_the_exponent() {
    let corpus = ladder_corpus();
    let mut coprime_pairs = 0u32;
    for a in &corpus {
        for b in &corpus {
            let (Some(ca), Some(cb)) = (a.cell(), b.cell()) else {
                continue;
            };
            let pa = ZPoly::from_coeffs(ca.poly_coeffs().to_vec());
            let pb = ZPoly::from_coeffs(cb.poly_coeffs().to_vec());
            let g = pa.gcd(&pb).unwrap();
            if g.degree() != Some(0) {
                continue;
            }
            coprime_pairs += 1;
            let fast = separation_exponent_for_pair(&pa, &pb, &g).unwrap();
            // The exact quantity the pre-ladder code computed.
            let slow =
                root_separation_exponent(&normalize_defining(&pa.mul(&pb)).unwrap()).unwrap();
            assert!(
                fast >= slow,
                "shortcut UNDERSTATED the separation exponent: {fast} < {slow}"
            );
        }
    }
    assert!(
        coprime_pairs >= 100,
        "corpus produced only {coprime_pairs} coprime pairs — the assertion above \
         would be vacuous"
    );
}

/// The ladder must answer exactly what an unconditional refinement to the proved
/// bound answers. This is the direct before/after equivalence check: it rebuilds
/// the pre-ladder decision (refine BOTH sides to `2^-(B+2)`, then read the order
/// off the disjoint intervals) and demands agreement on every ordered pair.
#[test]
fn the_ladder_agrees_with_an_unconditional_refinement_to_the_proved_bound() {
    let corpus = ladder_corpus();
    let mut compared = 0u32;
    for a in &corpus {
        for b in &corpus {
            let ord = a.cmp_anum(b).expect("comparison is total here");
            let (Some(ca), Some(cb)) = (a.cell(), b.cell()) else {
                continue;
            };
            let pa = ZPoly::from_coeffs(ca.poly_coeffs().to_vec());
            let pb = ZPoly::from_coeffs(cb.poly_coeffs().to_vec());
            let g = pa.gcd(&pb).unwrap();
            if g.degree() != Some(0) {
                // Equal-or-shared-factor pairs go through the certificate, which
                // the ladder does not touch.
                continue;
            }
            let b_bits =
                root_separation_exponent(&normalize_defining(&pa.mul(&pb)).unwrap()).unwrap();
            let target = Bq::inv_two_pow(b_bits + 2);
            let (ra, _) = mpbq::refine_to_width(ca.poly_coeffs(), ca.interval(), &target).unwrap();
            let (rb, _) = mpbq::refine_to_width(cb.poly_coeffs(), cb.interval(), &target).unwrap();
            let (Refined::Narrowed(ia), Refined::Narrowed(ib)) = (ra, rb) else {
                continue;
            };
            let reference = if ia.hi().cmp_bq(ib.lo()) != Ordering::Greater {
                Ordering::Less
            } else if ib.hi().cmp_bq(ia.lo()) != Ordering::Greater {
                Ordering::Greater
            } else {
                continue;
            };
            compared += 1;
            assert_eq!(
                ord,
                reference,
                "ladder disagreed with unconditional refinement to 2^-{}",
                b_bits + 2
            );
        }
    }
    assert!(compared >= 100, "only {compared} pairs compared — too weak");
}

/// The sign ladder's certificate must agree with an unconditional refinement to
/// the proved bound followed by a midpoint evaluation — the rule this function
/// used before the ladder existed.
#[test]
fn the_sign_ladder_agrees_with_the_midpoint_rule_at_the_proved_bound() {
    let corpus = ladder_corpus();
    let probes: Vec<Vec<BigInt>> = vec![
        zp(&[-3, 1]).coeffs().to_vec(),
        zp(&[1, 1]).coeffs().to_vec(),
        zp(&[-7, 0, 1]).coeffs().to_vec(),
        zp(&[-3, 1, -3, 1]).coeffs().to_vec(),
        zp(&[5, -2, 0, 1]).coeffs().to_vec(),
    ];
    let mut compared = 0u32;
    for a in &corpus {
        let Some(c) = a.cell() else { continue };
        for q in &probes {
            let s = a.sign_of_poly(q).expect("sign is total here");
            let qz = ZPoly::from_coeffs(q.clone());
            let qs = normalize_defining(&qz).unwrap();
            let pa = ZPoly::from_coeffs(c.poly_coeffs().to_vec());
            let g = pa.gcd(&qs).unwrap();
            if g.degree() != Some(0) {
                continue;
            }
            let b_bits =
                root_separation_exponent(&normalize_defining(&pa.mul(&qs)).unwrap()).unwrap();
            let target = Bq::inv_two_pow(b_bits + 1);
            let (r, _) = mpbq::refine_to_width(c.poly_coeffs(), c.interval(), &target).unwrap();
            let point = match r {
                Refined::Exact(m) => m,
                Refined::Narrowed(v) => v.midpoint().unwrap(),
            };
            let reference = mpbq::poly_sign_at(q, &point).unwrap();
            compared += 1;
            assert_eq!(s, reference, "sign ladder disagreed with the midpoint rule");
        }
    }
    assert!(compared >= 40, "only {compared} probes compared — too weak");
}

/// The ladder must never report more bisections than the liveness bound it
/// declares, on any pair — the invariant the oracle's `anum-compare` check reads
/// off the trace.
#[test]
fn the_ladder_never_exceeds_its_declared_liveness_bound() {
    let corpus = ladder_corpus();
    let mut seen = 0u32;
    for a in &corpus {
        for b in &corpus {
            let Some((_, t)) = a.cmp_anum_traced(b) else {
                continue;
            };
            seen += 1;
            assert!(
                t.steps_a <= t.bound && t.steps_b <= t.bound,
                "steps {}/{} exceeded bound {}",
                t.steps_a,
                t.steps_b,
                t.bound
            );
            if t.equal_by_certificate {
                assert_eq!((t.steps_a, t.steps_b), (0, 0), "certificate path bisected");
            }
        }
    }
    assert!(seen >= 150, "only {seen} traces seen");
}
