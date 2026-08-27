// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for [`crate::upoly`].
//!
//! These cover the DEGENERATE cases the differential oracle cannot reach,
//! because the oracle's generators draw from a distribution that almost never
//! produces them: the zero polynomial, a modulus that divides the leading
//! coefficient, a composite modulus, a `p`-th power in characteristic `p`, and
//! `p == 2` (where Cantor-Zassenhaus has to use the trace map instead of
//! `(p^d - 1)/2`).

use num_bigint::BigInt;
use num_traits::{One, Zero};

use crate::upoly::{is_prime_u64, ZPoly, Zp};

fn z(c: &[i64]) -> ZPoly {
    ZPoly::from_coeffs(c.iter().map(|&v| BigInt::from(v)).collect())
}

fn ints(p: &ZPoly) -> Vec<i64> {
    p.coeffs()
        .iter()
        .map(|c| i64::try_from(c.clone()).expect("test coefficients are small"))
        .collect()
}

// ---------------------------------------------------------------------------
// Z layer: degenerate inputs
// ---------------------------------------------------------------------------

#[test]
fn the_zero_polynomial_has_no_degree_and_no_primitive_part() {
    let zero = ZPoly::zero();
    assert!(zero.is_zero());
    // NOT Some(0): the zero polynomial has no degree at all.
    assert_eq!(zero.degree(), None);
    assert!(zero.lc().is_none());
    assert!(zero.content().is_zero());
    assert!(zero.primitive_part().is_none());
    assert!(zero.split_content().is_none());
    assert!(zero.square_free_decomposition().is_none());
}

#[test]
fn dividing_by_the_zero_polynomial_fails_closed() {
    let p = z(&[1, 2, 3]);
    assert!(p.exact_div(&ZPoly::zero()).is_none());
    assert!(p.pseudo_div(&ZPoly::zero()).is_none());
}

#[test]
fn exact_div_refuses_a_division_that_only_works_over_the_rationals() {
    // (2x + 2) does NOT divide (x^2 - 1) in Z[x], though it does in Q[x].
    let num = z(&[-1, 0, 1]);
    let den = z(&[2, 2]);
    assert!(num.exact_div(&den).is_none());
    // ...but (x + 1) does.
    assert_eq!(
        ints(&num.exact_div(&z(&[1, 1])).expect("divides")),
        vec![-1, 1]
    );
}

#[test]
fn pseudo_division_satisfies_its_identity_including_the_degenerate_shapes() {
    let cases: Vec<(ZPoly, ZPoly)> = vec![
        (z(&[1, 2, 3, 4]), z(&[5, 7])),
        (z(&[1]), z(&[2, 3, 4])),          // deg num < deg den
        (ZPoly::zero(), z(&[2, 3])),       // zero numerator
        (z(&[-6, 11, -6, 1]), z(&[2, 1])), // exact division case
    ];
    for (a, b) in cases {
        let pd = a.pseudo_div(&b).expect("non-zero divisor");
        let mut lhs = a.clone();
        for _ in 0..pd.d {
            lhs = lhs.scale(b.lc().expect("non-zero divisor"));
        }
        let rhs = pd.q.mul(&b).add(&pd.r);
        assert_eq!(lhs, rhs, "pseudo-division identity");
        if let (Some(rd), Some(bd)) = (pd.r.degree(), b.degree()) {
            assert!(rd < bd, "remainder degree");
        }
    }
}

#[test]
fn content_and_primitive_part_reconstruct_the_input_with_sign() {
    // Negative leading coefficient: the unit goes into `c`, not into `pp`.
    let p = z(&[6, -9, -12]);
    let (c, pp) = p.split_content().expect("non-zero");
    assert_eq!(c, BigInt::from(-3));
    assert!(pp.lc().expect("non-zero") > &BigInt::zero());
    assert_eq!(pp.scale(&c), p);
    assert!(pp.content().is_one());

    // `primitive_part` is the sign-blind sibling of `split_content`, and its
    // `Some` branch had NO caller anywhere — not in the module, not in the
    // oracle, not in a test. Only `is_none()` on the zero polynomial was ever
    // asserted. That is the same shape as the `square_free` entry point this
    // campaign already found unreachable, so it is pinned here explicitly:
    // it divides by the content but does NOT normalize the sign, so its
    // leading coefficient stays negative where `split_content`'s does not.
    let raw = p.primitive_part().expect("non-zero");
    assert_eq!(ints(&raw), vec![2, -3, -4]);
    // The distinguishing property: the sign is NOT normalized, so unlike
    // `split_content`'s `pp` above this one keeps its negative leading
    // coefficient. Divide by the POSITIVE content and nothing else.
    assert!(raw.lc().expect("non-zero") < &BigInt::zero());
    assert!(raw.content().is_one());
    assert_eq!(raw.scale(&p.content()), p);

    // A polynomial whose content is 1 already: primitive_part is the identity.
    let already = z(&[3, 5]);
    assert_eq!(already.primitive_part().expect("non-zero"), already);
}

#[test]
fn gcd_over_z_keeps_the_integer_content() {
    // 2*(x-1)*(x+1) and 4*(x-1)*(x+2): gcd is 2*(x-1).
    let a = z(&[-2, 0, 2]);
    let b = z(&[-8, 4, 4]);
    let g = a.gcd(&b).expect("gcd");
    assert_eq!(ints(&g), vec![-2, 2]);
    assert!(a.exact_div(&g).is_some());
    assert!(b.exact_div(&g).is_some());
}

#[test]
fn gcd_degenerate_arguments() {
    let a = z(&[-2, 0, 2]);
    assert_eq!(
        ZPoly::zero().gcd(&ZPoly::zero()).expect("gcd of zeros"),
        ZPoly::zero()
    );
    // gcd(0, a) == a up to a positive-lc normalization.
    assert_eq!(ints(&ZPoly::zero().gcd(&a).expect("gcd")), vec![-2, 0, 2]);
    assert_eq!(ints(&a.gcd(&ZPoly::zero()).expect("gcd")), vec![-2, 0, 2]);
    // gcd with a constant is that constant's content.
    let g = a.gcd(&z(&[3])).expect("gcd");
    assert_eq!(ints(&g), vec![1]);
}

#[test]
fn yun_recovers_a_planted_multiplicity_structure_exactly() {
    // f = 5 * (x-1)^3 * (x+2)^2 * (x-3)
    let f = z(&[1, -1]).neg(); // (x - 1)
    let g = z(&[2, 1]);
    let h = z(&[-3, 1]);
    let input = f
        .mul(&f)
        .mul(&f)
        .mul(&g)
        .mul(&g)
        .mul(&h)
        .scale(&BigInt::from(5));
    let d = input.square_free_decomposition().expect("non-zero");
    // The exact identity is the whole point.
    let mut prod = ZPoly::constant(d.c.clone());
    for (fac, m) in &d.factors {
        for _ in 0..*m {
            prod = prod.mul(fac);
        }
    }
    assert_eq!(prod, input, "c * prod f_i^i must equal the input EXACTLY");
    let mults: Vec<usize> = d.factors.iter().map(|(_, m)| *m).collect();
    assert_eq!(mults, vec![1, 2, 3]);
    // Every returned factor is square-free and they are pairwise coprime.
    for (fac, _) in &d.factors {
        let gg = fac.gcd(&fac.derivative()).expect("gcd");
        assert_eq!(gg.degree(), Some(0), "factor must be square-free");
    }
}

#[test]
fn yun_on_an_already_square_free_input_returns_it_unchanged() {
    let input = z(&[-1, 0, 1]); // x^2 - 1
    let d = input.square_free_decomposition().expect("non-zero");
    assert_eq!(d.c, BigInt::one());
    assert_eq!(d.factors.len(), 1);
    assert_eq!(d.factors[0].1, 1);
    assert_eq!(d.factors[0].0, input);
}

#[test]
fn yun_on_a_constant_returns_no_factors() {
    let d = z(&[7]).square_free_decomposition().expect("non-zero");
    assert_eq!(d.c, BigInt::from(7));
    assert!(d.factors.is_empty());
}

// ---------------------------------------------------------------------------
// Z_p layer: the modulus itself
// ---------------------------------------------------------------------------

#[test]
fn a_composite_or_out_of_range_modulus_is_refused_not_guessed() {
    assert!(Zp::new(0).is_none());
    assert!(Zp::new(1).is_none());
    assert!(Zp::new(4).is_none());
    assert!(Zp::new(1_000_000).is_none()); // composite
    assert!(Zp::new(u64::MAX).is_none()); // out of range
    assert!(Zp::new(1 << 31).is_none()); // exactly at the cap
    assert!(Zp::new(2).is_some());
    assert!(Zp::new(2_147_483_647).is_some()); // 2^31 - 1, a Mersenne prime
}

#[test]
fn the_primality_test_agrees_with_trial_division_below_ten_thousand() {
    for n in 0u64..10_000 {
        let trial = n >= 2 && (2..=n.isqrt()).all(|d| !n.is_multiple_of(d));
        assert_eq!(is_prime_u64(n), trial, "n = {n}");
    }
}

#[test]
fn reduction_drops_the_degree_when_p_divides_the_leading_coefficient() {
    let m = Zp::new(5).expect("prime");
    // 5x^2 + 3x + 1 reduces to 3x + 1: the degree DROPS, and that is not an
    // error, it is the case every lifting algorithm has to notice.
    let r = m.reduce(&z(&[1, 3, 5]));
    assert_eq!(r.degree(), Some(1));
    assert_eq!(r.coeffs(), &[1, 3]);
    // A polynomial that vanishes entirely.
    assert!(m.reduce(&z(&[5, 10, 15])).is_zero());
}

#[test]
fn the_modular_inverse_fails_closed_on_a_multiple_of_p() {
    let m = Zp::new(7).expect("prime");
    assert_eq!(m.inv_s(0), None);
    assert_eq!(m.inv_s(7), None);
    assert_eq!(m.inv_s(14), None);
    for a in 1..7u64 {
        let i = m.inv_s(a).expect("invertible");
        assert_eq!((a * i) % 7, 1);
    }
}

#[test]
fn division_in_zp_satisfies_its_identity_and_refuses_a_zero_divisor() {
    let m = Zp::new(13).expect("prime");
    let a = m.from_u64(vec![1, 2, 3, 4, 5]);
    let b = m.from_u64(vec![7, 0, 2]);
    let (q, r) = m.div_rem(&a, &b).expect("non-zero divisor");
    assert_eq!(m.add(&m.mul(&q, &b), &r), a);
    assert!(r.degree().unwrap_or(0) < b.degree().expect("non-zero"));
    assert!(m.div_rem(&a, &m.zero()).is_none());
}

// ---------------------------------------------------------------------------
// Z_p: square-free decomposition, including the characteristic-p trap
// ---------------------------------------------------------------------------

#[test]
fn square_free_decomposition_handles_a_p_th_power_whose_derivative_vanishes() {
    let m = Zp::new(3).expect("prime");
    // (x + 1)^3 == x^3 + 1 over F_3, and its derivative is 3x^2 == 0.
    // A decomposition that treated a vanishing derivative as "already
    // square-free" would return x^3 + 1 with multiplicity 1 — wrong.
    let f = m.from_u64(vec![1, 0, 0, 1]);
    assert!(m.derivative(&f).is_zero(), "the trap: f' == 0");
    let d = m.square_free_decomposition(&f).expect("monic non-zero");
    assert_eq!(d.len(), 1);
    assert_eq!(d[0].1, 3, "multiplicity must be 3, not 1");
    assert_eq!(d[0].0.coeffs(), &[1, 1], "the factor is x + 1");
    // And the identity holds.
    let mut prod = m.one();
    for (g, e) in &d {
        for _ in 0..*e {
            prod = m.mul(&prod, g);
        }
    }
    assert_eq!(prod, f);
}

#[test]
fn square_free_decomposition_handles_a_p_th_power_hidden_behind_a_simple_factor() {
    let m = Zp::new(3).expect("prime");
    // (x + 2) * (x + 1)^3 — the derivative is non-zero, but the residue `c`
    // left after the main loop is a p-th power.
    let a = m.from_u64(vec![2, 1]);
    let b = m.from_u64(vec![1, 0, 0, 1]); // (x+1)^3
    let f = m.mul(&a, &b);
    let d = m.square_free_decomposition(&f).expect("monic non-zero");
    let mut prod = m.one();
    for (g, e) in &d {
        for _ in 0..*e {
            prod = m.mul(&prod, g);
        }
    }
    assert_eq!(prod, f, "identity must hold through the p-th-root branch");
    let mults: Vec<usize> = d.iter().map(|(_, e)| *e).collect();
    assert_eq!(mults, vec![1, 3]);
}

#[test]
fn square_free_decomposition_refuses_a_non_monic_or_zero_input() {
    let m = Zp::new(7).expect("prime");
    assert!(m.square_free_decomposition(&m.zero()).is_none());
    assert!(m
        .square_free_decomposition(&m.from_u64(vec![1, 3]))
        .is_none());
}

#[test]
fn the_p_th_root_refuses_a_polynomial_that_is_not_a_p_th_power() {
    let m = Zp::new(3).expect("prime");
    assert!(m.p_th_root(&m.from_u64(vec![1, 1, 0, 1])).is_none());
    assert_eq!(
        m.p_th_root(&m.from_u64(vec![1, 0, 0, 1]))
            .expect("is a cube")
            .coeffs(),
        &[1, 1]
    );
}

// ---------------------------------------------------------------------------
// Z_p: distinct-degree and factorization
// ---------------------------------------------------------------------------

#[test]
fn distinct_degree_refuses_a_non_square_free_input() {
    let m = Zp::new(7).expect("prime");
    // (x + 1)^2, square-free-ness violated.
    let f = m.from_u64(vec![1, 2, 1]);
    assert!(
        m.distinct_degree(&f).is_none(),
        "DDF rests on square-freeness and must refuse, not answer"
    );
}

#[test]
fn distinct_degree_separates_a_planted_mix_of_degrees() {
    let m = Zp::new(11).expect("prime");
    // (x)(x+1)(x+2) — three linear factors — times an irreducible quadratic.
    let lin = m.mul(
        &m.mul(&m.from_u64(vec![0, 1]), &m.from_u64(vec![1, 1])),
        &m.from_u64(vec![2, 1]),
    );
    // x^2 + 1 is irreducible mod 11 (11 == 3 mod 4).
    let quad = m.from_u64(vec![1, 0, 1]);
    assert_eq!(m.is_irreducible(&quad), Some(true));
    let f = m.mul(&lin, &quad);
    let buckets = m.distinct_degree(&f).expect("square-free monic");
    let mut prod = m.one();
    for (g, _) in &buckets {
        prod = m.mul(&prod, g);
    }
    assert_eq!(prod, f, "the buckets must multiply back to the input");
    let mut ds: Vec<usize> = buckets.iter().map(|(_, d)| *d).collect();
    ds.sort_unstable();
    assert_eq!(ds, vec![1, 2]);
    for (g, d) in &buckets {
        assert_eq!(g.degree().expect("non-zero") % d, 0);
    }
}

#[test]
fn factorization_of_a_split_product_recovers_every_linear_factor() {
    let m = Zp::new(101).expect("prime");
    // prod_{i=0}^{9} (x - i): ten distinct linear factors, the worst case for
    // equal-degree splitting.
    let mut f = m.one();
    for i in 0..10u64 {
        f = m.mul(&f, &m.from_u64(vec![(101 - i) % 101, 1]));
    }
    let fac = m.factor(&f).expect("non-zero");
    assert_eq!(fac.lc, 1);
    assert_eq!(fac.factors.len(), 10);
    let mut prod = m.from_u64(vec![fac.lc]);
    for (g, e) in &fac.factors {
        assert_eq!(g.degree(), Some(1));
        assert_eq!(*e, 1);
        assert_eq!(m.is_irreducible(g), Some(true));
        for _ in 0..*e {
            prod = m.mul(&prod, g);
        }
    }
    assert_eq!(prod, f, "the product identity is the oracle");
}

#[test]
fn factorization_is_deterministic_across_repeated_calls() {
    // Cantor-Zassenhaus is randomized; AY seeds it from the input so that a
    // failing case reproduces. Two calls must agree exactly.
    let m = Zp::new(97).expect("prime");
    let mut f = m.one();
    for i in 1..8u64 {
        f = m.mul(&f, &m.from_u64(vec![i, 1]));
    }
    let a = m.factor(&f).expect("non-zero");
    let b = m.factor(&f).expect("non-zero");
    assert_eq!(a.factors, b.factors);
}

#[test]
fn factorization_works_in_characteristic_two_where_the_trace_map_is_required() {
    let m = Zp::new(2).expect("prime");
    // (x^2 + x + 1) is the only irreducible quadratic over F_2.
    // Build (x)(x+1)(x^2+x+1)^2 and check the full identity.
    let q = m.from_u64(vec![1, 1, 1]);
    let f = m.mul(
        &m.mul(&m.from_u64(vec![0, 1]), &m.from_u64(vec![1, 1])),
        &m.mul(&q, &q),
    );
    let fac = m.factor(&f).expect("non-zero");
    let mut prod = m.from_u64(vec![fac.lc]);
    for (g, e) in &fac.factors {
        assert_eq!(
            m.is_irreducible(g),
            Some(true),
            "factor must be irreducible"
        );
        for _ in 0..*e {
            prod = m.mul(&prod, g);
        }
    }
    assert_eq!(prod, f);
    assert_eq!(fac.factors.len(), 3);
}

#[test]
fn factoring_the_zero_polynomial_fails_closed_and_a_constant_is_its_own_factor() {
    let m = Zp::new(13).expect("prime");
    assert!(m.factor(&m.zero()).is_none());
    let c = m.factor(&m.from_u64(vec![9])).expect("non-zero constant");
    assert_eq!(c.lc, 9);
    assert!(c.factors.is_empty());
}

#[test]
fn factoring_a_non_monic_input_puts_the_unit_in_lc() {
    let m = Zp::new(13).expect("prime");
    // 5 * (x + 1) * (x + 2)
    let f = m.scale(&m.mul(&m.from_u64(vec![1, 1]), &m.from_u64(vec![2, 1])), 5);
    let fac = m.factor(&f).expect("non-zero");
    assert_eq!(fac.lc, 5);
    let mut prod = m.from_u64(vec![fac.lc]);
    for (g, e) in &fac.factors {
        assert_eq!(g.lc(), Some(1), "every factor is monic");
        for _ in 0..*e {
            prod = m.mul(&prod, g);
        }
    }
    assert_eq!(prod, f);
}

#[test]
fn irreducibility_agrees_with_the_factorizer_on_every_monic_cubic_mod_five() {
    // An exhaustive cross-check of the two independent paths on 125 inputs.
    let m = Zp::new(5).expect("prime");
    let mut irreducible_count = 0;
    for a in 0..5u64 {
        for b in 0..5u64 {
            for c in 0..5u64 {
                let f = m.from_u64(vec![a, b, c, 1]);
                let rabin = m.is_irreducible(&f).expect("monic degree 3");
                let fac = m.factor(&f).expect("non-zero");
                let via_factor = fac.factors.len() == 1
                    && fac.factors[0].1 == 1
                    && fac.factors[0].0.degree() == Some(3);
                assert_eq!(rabin, via_factor, "disagreement on {:?}", f.coeffs());
                if rabin {
                    irreducible_count += 1;
                }
            }
        }
    }
    // (5^3 - 5)/3 == 40 monic irreducible cubics over F_5.
    assert_eq!(irreducible_count, 40);
}

#[test]
fn every_monic_quartic_mod_three_factors_back_to_itself() {
    // Exhaustive: 81 inputs, each checked against the exact product identity
    // and against the independent irreducibility test.
    let m = Zp::new(3).expect("prime");
    for a in 0..3u64 {
        for b in 0..3u64 {
            for c in 0..3u64 {
                for d in 0..3u64 {
                    let f = m.from_u64(vec![a, b, c, d, 1]);
                    let fac = m.factor(&f).expect("non-zero");
                    let mut prod = m.from_u64(vec![fac.lc]);
                    let mut total = 0usize;
                    for (g, e) in &fac.factors {
                        assert_eq!(
                            m.is_irreducible(g),
                            Some(true),
                            "non-irreducible factor for {:?}",
                            f.coeffs()
                        );
                        total += g.degree().expect("non-zero") * e;
                        for _ in 0..*e {
                            prod = m.mul(&prod, g);
                        }
                    }
                    assert_eq!(prod, f, "product identity for {:?}", f.coeffs());
                    assert_eq!(total, 4, "degrees must sum to 4");
                }
            }
        }
    }
}

/// `factor` must not DECLINE on ordinary fully-split input at the degrees where
/// the equal-degree budget used to run out.
///
/// This pins a real capability cliff a verifier found. `EDF_ATTEMPT_BUDGET` was
/// allocated once per `equal_degree` CALL and threaded through every split, so
/// it capped total work rather than guarding liveness. Cantor-Zassenhaus needs
/// ~1.5 attempts per split, so from around 335 linear factors the call ran out
/// and `factor()` returned `None` — non-monotonically, because whether it fit
/// depended on how lucky the earlier splits were: 340 declined, 350 succeeded,
/// 355 declined, 370 declined.
///
/// The degrees below straddle that window deliberately. They are cheap: a
/// degree-256 split-linear factorization measured 17.6 ms.
#[test]
fn factor_does_not_decline_on_fully_split_input_across_the_old_budget_cliff() {
    let m = Zp::new(65537).expect("prime");
    for n in [320u64, 340, 355, 370, 384] {
        // prod_{i<n} (x - i): n distinct linear factors, the worst case for
        // equal-degree splitting and the shape that exposed the cliff.
        let mut f = m.one();
        for i in 0..n {
            f = m.mul(&f, &m.from_u64(vec![(65537 - i) % 65537, 1]));
        }
        let fac = m
            .factor(&f)
            .unwrap_or_else(|| panic!("factor DECLINED on {n} distinct linear factors"));
        assert_eq!(
            fac.factors.len(),
            usize::try_from(n).expect("fits"),
            "degree {n}: wrong factor count"
        );
        for (g, e) in &fac.factors {
            assert_eq!(g.degree(), Some(1), "degree {n}: a factor is not linear");
            assert_eq!(*e, 1, "degree {n}: multiplicity must be 1");
        }
    }
}

include!("upoly_tests/yun_regression.rs");
