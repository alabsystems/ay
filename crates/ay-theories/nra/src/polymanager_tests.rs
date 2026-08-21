// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for [`crate::polymanager`].
//!
//! These pin the invariants and the degenerate inputs; the RANDOMIZED
//! agreement testing lives in `crates/ay-nra-oracle` and is compared against
//! z3, not against a second copy of the same reasoning.

use super::*;

/// A manager plus the three variables the tests use.
struct Ctx {
    m: PolyManager,
    x: PVar,
    y: PVar,
    z: PVar,
}

impl Ctx {
    fn new() -> Self {
        Self {
            m: PolyManager::new(),
            x: 0,
            y: 1,
            z: 2,
        }
    }
    fn c(&self, k: i64) -> Poly {
        self.m.mk_const(BigInt::from(k))
    }
    /// `k * x^a * y^b * z^c`
    fn t(&mut self, k: i64, a: u32, b: u32, cc: u32) -> Poly {
        let (x, y, z) = (self.x, self.y, self.z);
        self.m
            .mk_from_pairs(&[(vec![(x, a), (y, b), (z, cc)], BigInt::from(k))])
    }
    fn add(&mut self, a: &Poly, b: &Poly) -> Poly {
        self.m.add(a, b)
    }
    fn mul(&mut self, a: &Poly, b: &Poly) -> Poly {
        self.m.mul(a, b)
    }
}

// ---------------------------------------------------------------------------
// 1. Representation
// ---------------------------------------------------------------------------

#[test]
fn monomials_are_interned_so_equality_is_a_u32_compare() {
    let mut m = PolyManager::new();
    let a = m.mk_mono(&[(0, 2), (1, 3)]);
    let b = m.mk_mono(&[(1, 3), (0, 2)]);
    let c = m.mk_mono(&[(0, 1), (0, 1), (1, 3)]);
    assert_eq!(a, b, "argument order must not create a second monomial");
    assert_eq!(a, c, "duplicate variables must be merged before interning");
    let d = m.mk_mono(&[(0, 2), (1, 4)]);
    assert_ne!(a, d);
}

#[test]
fn zero_exponents_collapse_to_the_constant_monomial() {
    let mut m = PolyManager::new();
    let one = m.mono_one();
    assert_eq!(m.mk_mono(&[]), one);
    assert_eq!(m.mk_mono(&[(0, 0), (5, 0)]), one);
    assert_eq!(m.mono_total_degree(one), 0);
}

#[test]
fn the_monomial_order_is_graded_then_high_variable_first() {
    let mut m = PolyManager::new();
    let x2 = m.mk_mono(&[(0, 2)]);
    let xy = m.mk_mono(&[(0, 1), (1, 1)]);
    let y2 = m.mk_mono(&[(1, 2)]);
    let x3 = m.mk_mono(&[(0, 3)]);
    // Graded first: total degree 3 beats every degree-2 monomial.
    assert_eq!(m.cmp_mono(x3, y2), Ordering::Greater);
    // Within a degree, the higher variable index wins.
    assert_eq!(m.cmp_mono(y2, xy), Ordering::Greater);
    assert_eq!(m.cmp_mono(xy, x2), Ordering::Greater);
    // Antisymmetry and reflexivity.
    assert_eq!(m.cmp_mono(x2, y2), Ordering::Less);
    assert_eq!(m.cmp_mono(x2, x2), Ordering::Equal);
}

#[test]
fn the_order_is_multiplicative_which_is_what_makes_exact_div_terminate() {
    let mut m = PolyManager::new();
    let pairs = [
        (vec![(0u32, 1u32)], vec![(1u32, 1u32)]),
        (vec![(0, 3)], vec![(0, 1), (1, 2)]),
        (vec![(1, 2), (2, 1)], vec![(2, 3)]),
    ];
    let mult = m.mk_mono(&[(0, 2), (1, 1), (2, 4)]);
    for (a, b) in pairs {
        let ma = m.mk_mono(&a);
        let mb = m.mk_mono(&b);
        let base = m.cmp_mono(ma, mb);
        let pa = m.mono_mul(ma, mult);
        let pb = m.mono_mul(mb, mult);
        assert_eq!(
            base,
            m.cmp_mono(pa, pb),
            "order must survive multiplication"
        );
    }
}

#[test]
fn canonical_form_makes_equality_structural() {
    let mut c = Ctx::new();
    let a = c.t(3, 1, 1, 0);
    let b = c.t(-3, 1, 1, 0);
    let sum = c.add(&a, &b);
    assert!(
        sum.is_zero(),
        "cancelling terms must be dropped, not stored"
    );

    let p1 = c.m.mk_from_pairs(&[
        (vec![(0, 1)], BigInt::from(2)),
        (vec![(1, 1)], BigInt::from(3)),
        (vec![(0, 1)], BigInt::from(5)),
    ]);
    let p2 = c.m.mk_from_pairs(&[
        (vec![(1, 1)], BigInt::from(3)),
        (vec![(0, 1)], BigInt::from(7)),
    ]);
    assert_eq!(p1, p2, "like terms must be merged into one canonical form");
    assert_eq!(p1.len(), 2);
    // Descending order: y (higher variable) leads.
    assert_eq!(c.m.mono_pows(p1.terms()[0].0), &[(1, 1)]);
}

#[test]
fn degree_and_leading_coefficient_queries() {
    let mut c = Ctx::new();
    // p = 3 x^2 y + 5 x z^3 - 7
    let a = c.t(3, 2, 1, 0);
    let b = c.t(5, 1, 0, 3);
    let d = c.c(-7);
    let p = c.add(&a, &b);
    let p = c.add(&p, &d);
    assert_eq!(c.m.degree(&p, c.x), 2);
    assert_eq!(c.m.degree(&p, c.y), 1);
    assert_eq!(c.m.degree(&p, c.z), 3);
    assert_eq!(c.m.degree(&p, 9), 0, "an absent variable has degree 0");
    assert_eq!(c.m.max_var(&p), Some(2));
    assert_eq!(c.m.vars(&p), vec![0, 1, 2]);
    assert_eq!(c.m.total_degree(&p), 4);

    let x = c.x;
    let lc = c.m.lc(&p, x);
    let expect = c.t(3, 0, 1, 0);
    assert_eq!(lc, expect, "lc(p, x) must be 3y");
}

#[test]
fn x_coeffs_round_trips_and_reassembles_the_polynomial() {
    let mut c = Ctx::new();
    let a = c.t(3, 2, 1, 0);
    let b = c.t(5, 1, 0, 3);
    let d = c.t(-7, 0, 2, 0);
    let p = c.add(&a, &b);
    let p = c.add(&p, &d);
    let x = c.x;
    let cs = c.m.x_coeffs(&p, x);
    assert_eq!(cs.len(), 3, "deg_x = 2 gives three coefficients");
    let back = c.m.from_x_coeffs(x, &cs);
    assert_eq!(back, p);
    // And each bucket is what `coeff` says it is.
    for (k, ck) in cs.iter().enumerate() {
        let direct = c.m.coeff(&p, x, k as u32);
        assert_eq!(&direct, ck);
    }
}

#[test]
fn degenerate_inputs_are_answered_not_assumed() {
    let mut c = Ctx::new();
    let zero = c.m.zero();
    let one = c.m.one();
    assert!(c.m.is_const(&zero));
    assert_eq!(c.m.max_var(&zero), None);
    assert_eq!(c.m.degree(&zero, c.x), 0);
    assert_eq!(c.m.vars(&zero), Vec::<PVar>::new());
    assert_eq!(c.m.const_value(&zero), Some(BigInt::zero()));
    let x = c.x;
    assert_eq!(c.m.lc(&zero, x), zero, "lc of zero is zero");
    // Division by zero refuses.
    assert!(c.m.exact_div(&one, &zero).is_none());
    assert!(c.m.exact_div_int(&one, &BigInt::zero()).is_none());
    // Pseudo-division by zero refuses.
    assert!(c
        .m
        .pseudo_division(&one, &zero, x, PseudoMode::Exact)
        .is_none());
    // Square-free of zero is zero; of a constant is itself.
    assert_eq!(c.m.square_free(&zero).unwrap(), zero);
    let five = c.c(5);
    assert_eq!(c.m.square_free(&five).unwrap(), five);
    assert_eq!(c.m.square_free_in(&zero, x).unwrap(), zero);
    // gcd(0, 0) == 0.
    assert_eq!(c.m.gcd(&zero, &zero).unwrap(), zero);
}

#[test]
fn exact_div_refuses_a_rational_quotient() {
    let mut c = Ctx::new();
    let two_x = c.t(2, 1, 0, 0);
    let four = c.c(4);
    assert!(
        c.m.exact_div(&two_x, &four).is_none(),
        "(2x)/4 is not in Z[x] and must be refused"
    );
    let eight_x = c.t(8, 1, 0, 0);
    let q = c.m.exact_div(&eight_x, &four).unwrap();
    let expect = c.t(2, 1, 0, 0);
    assert_eq!(q, expect);
}

#[test]
fn exact_div_is_the_inverse_of_mul_on_a_built_product() {
    let mut c = Ctx::new();
    // a = x^2 y - 3 z + 1, b = x z^2 + 5 y
    let a1 = c.t(1, 2, 1, 0);
    let a2 = c.t(-3, 0, 0, 1);
    let a3 = c.c(1);
    let a = c.add(&a1, &a2);
    let a = c.add(&a, &a3);
    let b1 = c.t(1, 1, 0, 2);
    let b2 = c.t(5, 0, 1, 0);
    let b = c.add(&b1, &b2);
    let prod = c.mul(&a, &b);
    assert_eq!(c.m.exact_div(&prod, &a).unwrap(), b);
    assert_eq!(c.m.exact_div(&prod, &b).unwrap(), a);
    let bump = c.add(&prod, &a3);
    assert!(
        c.m.exact_div(&bump, &a).is_none() || c.m.exact_div(&bump, &a).unwrap() != b,
        "a perturbed product must not divide"
    );
}

// ---------------------------------------------------------------------------
// 2. Pseudo-division
// ---------------------------------------------------------------------------

/// The defining identity, checked with the manager's own arithmetic.
fn check_pseudo(c: &mut Ctx, p: &Poly, q: &Poly, x: PVar, mode: PseudoMode) -> PseudoDiv {
    let r = c.m.pseudo_division(p, q, x, mode).expect("q is non-zero");
    let l = c.m.lc(q, x);
    let lp = c.m.pow(&l, r.d);
    let lhs = c.m.mul(&lp, p);
    let qq = c.m.mul(&r.quot, q);
    let rhs = c.m.add(&qq, &r.rem);
    assert_eq!(lhs, rhs, "lc^d * p == Q*q + R must hold exactly");
    if !r.rem.is_zero() {
        assert!(
            c.m.degree(&r.rem, x) < c.m.degree(q, x),
            "the remainder must be reduced in x"
        );
    }
    r
}

#[test]
fn pseudo_division_identity_univariate() {
    let mut c = Ctx::new();
    let x = c.x;
    // p = 3x^4 - x^2 + 7, q = 2x^2 + 5
    let p = {
        let a = c.t(3, 4, 0, 0);
        let b = c.t(-1, 2, 0, 0);
        let d = c.c(7);
        let s = c.add(&a, &b);
        c.add(&s, &d)
    };
    let q = {
        let a = c.t(2, 2, 0, 0);
        let b = c.c(5);
        c.add(&a, &b)
    };
    let e = check_pseudo(&mut c, &p, &q, x, PseudoMode::Exact);
    assert_eq!(e.d, 4 - 2 + 1, "Exact mode pins d = deg p - deg q + 1");
    let l = check_pseudo(&mut c, &p, &q, x, PseudoMode::Loose);
    assert!(l.d <= e.d);
}

#[test]
fn pseudo_division_identity_multivariate() {
    let mut c = Ctx::new();
    let x = c.x;
    // p = y x^3 + z x - 4, q = (z+1) x^2 + y
    let p = {
        let a = c.t(1, 3, 1, 0);
        let b = c.t(1, 1, 0, 1);
        let d = c.c(-4);
        let s = c.add(&a, &b);
        c.add(&s, &d)
    };
    let q = {
        let a = c.t(1, 2, 0, 1);
        let b = c.t(1, 2, 0, 0);
        let d = c.t(1, 0, 1, 0);
        let s = c.add(&a, &b);
        c.add(&s, &d)
    };
    check_pseudo(&mut c, &p, &q, x, PseudoMode::Exact);
    check_pseudo(&mut c, &p, &q, x, PseudoMode::Loose);
}

#[test]
fn pseudo_division_when_the_divisor_is_free_of_x() {
    let mut c = Ctx::new();
    let x = c.x;
    let p = {
        let a = c.t(3, 2, 0, 0);
        let b = c.c(1);
        c.add(&a, &b)
    };
    // q = y + 2 : deg_x(q) == 0, so lc(q, x) == q and the remainder is zero.
    let q = {
        let a = c.t(1, 0, 1, 0);
        let b = c.c(2);
        c.add(&a, &b)
    };
    let r = check_pseudo(&mut c, &p, &q, x, PseudoMode::Exact);
    assert!(r.rem.is_zero());
    assert_eq!(r.d, 3, "deg_x(p) + 1");
    let l = check_pseudo(&mut c, &p, &q, x, PseudoMode::Loose);
    assert_eq!(l.d, 1);
    assert_eq!(l.quot, p);
}

#[test]
fn pseudo_division_when_the_dividend_has_the_smaller_degree() {
    // z3's own `pseudo_division_core` underflows here; this manager answers.
    let mut c = Ctx::new();
    let x = c.x;
    let p = c.t(5, 1, 0, 0);
    let q = {
        let a = c.t(2, 3, 0, 0);
        let b = c.c(1);
        c.add(&a, &b)
    };
    let r = check_pseudo(&mut c, &p, &q, x, PseudoMode::Exact);
    assert_eq!(r.d, 0);
    assert!(r.quot.is_zero());
    assert_eq!(r.rem, p);
}

#[test]
fn pseudo_division_with_a_vanishing_leading_coefficient_in_the_dividend() {
    // p's leading x-coefficient is `y`, which the pseudo-division must treat as
    // a ring element that may itself vanish under specialization; the identity
    // is still exact in Z[y][x].
    let mut c = Ctx::new();
    let x = c.x;
    let p = {
        let a = c.t(1, 2, 1, 0);
        let b = c.t(1, 1, 0, 0);
        c.add(&a, &b)
    };
    let q = {
        let a = c.t(1, 1, 0, 1);
        let b = c.c(-1);
        c.add(&a, &b)
    };
    check_pseudo(&mut c, &p, &q, x, PseudoMode::Exact);
}

// ---------------------------------------------------------------------------
// 3. GCD
// ---------------------------------------------------------------------------

#[test]
fn gcd_of_a_built_product_recovers_the_common_factor() {
    let mut c = Ctx::new();
    // g = x y - 2 z ; u = g * (x + 1) ; v = g * (y - 3)
    let g = {
        let a = c.t(1, 1, 1, 0);
        let b = c.t(-2, 0, 0, 1);
        c.add(&a, &b)
    };
    let f1 = {
        let a = c.t(1, 1, 0, 0);
        let b = c.c(1);
        c.add(&a, &b)
    };
    let f2 = {
        let a = c.t(1, 0, 1, 0);
        let b = c.c(-3);
        c.add(&a, &b)
    };
    let u = c.mul(&g, &f1);
    let v = c.mul(&g, &f2);
    let got = c.m.gcd(&u, &v).unwrap();
    assert_eq!(got, g, "PRS gcd must recover the planted factor exactly");
    // And the modular path must agree.
    let got_m = c.m.mod_gcd(&u, &v).unwrap();
    assert_eq!(got_m, g, "modular gcd must agree with the PRS gcd");
}

#[test]
fn gcd_is_normalized_to_a_positive_leading_coefficient() {
    let mut c = Ctx::new();
    let g = {
        let a = c.t(-1, 1, 1, 0);
        let b = c.t(2, 0, 0, 1);
        c.add(&a, &b)
    };
    let f1 = c.t(3, 1, 0, 0);
    let f2 = c.t(5, 0, 1, 0);
    let u = c.mul(&g, &f1);
    let v = c.mul(&g, &f2);
    let got = c.m.gcd(&u, &v).unwrap();
    assert!(
        !got.terms()[0].1.is_negative(),
        "the unit ambiguity must be pinned down"
    );
    let neg = c.m.neg(&got);
    assert!(got == g || neg == g);
}

#[test]
fn gcd_of_coprime_inputs_is_the_integer_content() {
    let mut c = Ctx::new();
    let u = {
        let a = c.t(6, 2, 0, 0);
        let b = c.c(6);
        c.add(&a, &b)
    };
    let v = {
        let a = c.t(4, 1, 0, 0);
        let b = c.c(-4);
        c.add(&a, &b)
    };
    // u = 6(x^2+1), v = 4(x-1); the polynomial parts are coprime.
    let g = c.m.gcd(&u, &v).unwrap();
    assert_eq!(g, c.c(2));
}

#[test]
fn gcd_degenerate_arguments() {
    let mut c = Ctx::new();
    let zero = c.m.zero();
    let p = {
        let a = c.t(-3, 2, 1, 0);
        let b = c.c(6);
        c.add(&a, &b)
    };
    // gcd(0, p) == normalized p.
    let g = c.m.gcd(&zero, &p).unwrap();
    let flipped = c.m.flip_sign_if_lm_neg(&p);
    assert_eq!(g, flipped);
    assert_eq!(c.m.gcd(&p, &zero).unwrap(), flipped);
    // gcd(p, p) == normalized p.
    assert_eq!(c.m.gcd(&p, &p).unwrap(), flipped);
    // gcd(const, p) is the integer gcd.
    let six = c.c(6);
    assert_eq!(c.m.gcd(&six, &p).unwrap(), c.c(3));
}

#[test]
fn content_and_primitive_part_reconstruct_the_input() {
    let mut c = Ctx::new();
    let x = c.x;
    // p = 6 y^2 x^2 + 9 y^2 x  =  3 * y^2 * (2x^2 + 3x)
    let p = {
        let a = c.t(6, 2, 2, 0);
        let b = c.t(9, 1, 2, 0);
        c.add(&a, &b)
    };
    let ic = c.m.iccp(&p, x).unwrap();
    let back = c.m.mul(&ic.c, &ic.pp);
    let back = c.m.mul_int(&back, &ic.i);
    assert_eq!(back, p, "p == i * c * pp must hold exactly");
    assert_eq!(ic.i, BigInt::from(3));
    assert_eq!(c.m.degree(&ic.c, x), 0, "the content is free of x");
    // The primitive part has trivial content.
    let ic2 = c.m.iccp(&ic.pp, x).unwrap();
    assert!(c.m.is_const(&ic2.c));
    assert_eq!(ic2.i, BigInt::one());
}

#[test]
fn iccp_of_degenerate_inputs() {
    let mut c = Ctx::new();
    let x = c.x;
    let zero = c.m.zero();
    let ic = c.m.iccp(&zero, x).unwrap();
    assert_eq!(ic.i, BigInt::zero());
    assert_eq!(ic.c, c.m.one());
    assert!(ic.pp.is_zero());

    let five = c.c(-5);
    let ic = c.m.iccp(&five, x).unwrap();
    assert_eq!(ic.i, BigInt::from(-5));
    assert_eq!(ic.c, c.m.one());
    assert_eq!(ic.pp, c.m.one());

    // Free of x: everything lands in i and c.
    let q = {
        let a = c.t(4, 0, 1, 0);
        let b = c.t(6, 0, 0, 1);
        c.add(&a, &b)
    };
    let ic = c.m.iccp(&q, x).unwrap();
    assert_eq!(ic.i, BigInt::from(2));
    assert_eq!(ic.pp, c.m.one());
    let back = c.m.mul_int(&ic.c, &ic.i);
    assert_eq!(back, q);
}

#[test]
fn modular_and_prs_gcd_agree_on_a_three_variable_family() {
    let mut c = Ctx::new();
    let cases: [(i64, u32, u32, u32, i64, u32, u32, u32); 4] = [
        (1, 1, 1, 0, -2, 0, 0, 1),
        (3, 2, 0, 1, 5, 0, 1, 0),
        (7, 1, 0, 0, -11, 0, 2, 1),
        (2, 0, 3, 0, 9, 1, 0, 2),
    ];
    for (k1, a1, b1, c1, k2, a2, b2, c2) in cases {
        let ga = c.t(k1, a1, b1, c1);
        let gb = c.t(k2, a2, b2, c2);
        let g = c.add(&ga, &gb);
        let fa = c.t(1, 1, 0, 1);
        let fb = c.c(3);
        let f1 = c.add(&fa, &fb);
        let f2a = c.t(4, 0, 1, 0);
        let f2b = c.c(-7);
        let f2 = c.add(&f2a, &f2b);
        let u = c.mul(&g, &f1);
        let v = c.mul(&g, &f2);
        let prs = c.m.gcd(&u, &v).unwrap();
        let modular = c.m.mod_gcd(&u, &v);
        if let Some(mg) = modular {
            assert_eq!(mg, prs, "modular and PRS gcd must not disagree");
        }
        // The PRS answer must at least divide both, whatever it is.
        assert!(c.m.divides(&prs, &u));
        assert!(c.m.divides(&prs, &v));
    }
}

// ---------------------------------------------------------------------------
// 4. Square-free
// ---------------------------------------------------------------------------

#[test]
fn square_free_in_removes_a_planted_repeated_factor() {
    let mut c = Ctx::new();
    let x = c.x;
    // p = (x - y)^2 * (x + 1)
    let f = {
        let a = c.t(1, 1, 0, 0);
        let b = c.t(-1, 0, 1, 0);
        c.add(&a, &b)
    };
    let f2 = c.mul(&f, &f);
    let g = {
        let a = c.t(1, 1, 0, 0);
        let b = c.c(1);
        c.add(&a, &b)
    };
    let p = c.mul(&f2, &g);
    let sf = c.m.square_free_in(&p, x).unwrap();
    let expect = c.mul(&f, &g);
    // Up to the documented unit: the answer is `p / g` with `g` the
    // sign-normalized gcd, so removing a repeated factor may negate the result.
    let neg_expect = c.m.neg(&expect);
    assert!(
        sf == expect || sf == neg_expect,
        "one copy of the repeated factor must survive (up to sign): {sf:?}"
    );
    assert!(
        c.m.is_square_free_in(&sf, x).unwrap(),
        "the operation must be idempotent"
    );
    assert!(!c.m.is_square_free_in(&p, x).unwrap());
    // The square-free part always divides the input.
    assert!(c.m.divides(&sf, &p));
}

#[test]
fn square_free_in_leaves_an_already_square_free_polynomial_alone() {
    let mut c = Ctx::new();
    let x = c.x;
    let p = {
        let a = c.t(1, 2, 0, 0);
        let b = c.t(1, 0, 1, 0);
        c.add(&a, &b)
    };
    assert_eq!(c.m.square_free_in(&p, x).unwrap(), p);
    assert!(c.m.is_square_free_in(&p, x).unwrap());
}

#[test]
fn square_free_in_a_variable_the_polynomial_does_not_mention() {
    let mut c = Ctx::new();
    let p = {
        let a = c.t(1, 2, 0, 0);
        let b = c.c(-4);
        c.add(&a, &b)
    };
    let z = c.z;
    assert_eq!(
        c.m.square_free_in(&p, z).unwrap(),
        p,
        "no square in an absent variable"
    );
}

#[test]
fn whole_polynomial_square_free_recurses_into_the_content() {
    let mut c = Ctx::new();
    // p = 6 * y^2 * (x - 1)^2 : squares in BOTH the content and the primitive
    // part, and a NON-UNIT integer content.
    //
    // The scalar 6 is the whole point. This test previously used an all-±1
    // input, and a verifier proved that made it vacuous: dropping the integer
    // content from `square_free` — returning `y(x-1)` where the answer is
    // `6y(x-1)` — passed it, passed all 30 unit tests, and produced ZERO oracle
    // divergences over 4,000 cases. An integer scalar divides, preserves every
    // real root and preserves square-freeness, so it is invisible to every leg
    // except an exact one. Keep this input non-monic.
    let f = {
        let a = c.t(1, 1, 0, 0);
        let b = c.c(-1);
        c.add(&a, &b)
    };
    let f2 = c.mul(&f, &f);
    let y2 = c.t(6, 0, 2, 0);
    let p = c.mul(&y2, &f2);
    let sf = c.m.square_free(&p).unwrap();
    let y1 = c.t(6, 0, 1, 0);
    let expect = c.mul(&y1, &f);
    assert_eq!(sf, expect);
    assert!(c.m.divides(&sf, &p));
    // Gauss's lemma, stated as the oracle states it: the integer content is
    // carried through EXACTLY.
    assert_eq!(c.m.int_content(&sf), c.m.int_content(&p));
    assert_eq!(c.m.int_content(&sf), num_bigint::BigInt::from(6));
}

/// The integer content of `square_free(p)` equals that of `p` — the identity
/// the whole-polynomial oracle check leans on, pinned here on inputs whose
/// content is deliberately non-trivial.
#[test]
fn whole_polynomial_square_free_preserves_the_integer_content() {
    for scale in [2i64, 6, 30, -12] {
        let mut c = Ctx::new();
        let f = {
            let a = c.t(1, 1, 0, 0);
            let b = c.c(-1);
            c.add(&a, &b)
        };
        let f2 = c.mul(&f, &f);
        let g = {
            let a = c.t(1, 0, 1, 0);
            let b = c.c(2);
            c.add(&a, &b)
        };
        let base = c.mul(&f2, &g);
        let p = c.m.mul_int(&base, &num_bigint::BigInt::from(scale));
        let sf = c.m.square_free(&p).unwrap();
        assert_eq!(
            c.m.int_content(&sf),
            c.m.int_content(&p),
            "scale {scale}: square_free changed the integer content"
        );
        assert!(c.m.divides(&sf, &p), "scale {scale}: sf must divide p");
        // The square really went away.
        assert!(
            c.m.total_degree(&sf) < c.m.total_degree(&p),
            "scale {scale}"
        );
    }
}

// ---------------------------------------------------------------------------
// Modular layer
// ---------------------------------------------------------------------------

/// The `pp_u` half of the modular acceptance certificate rejects a candidate
/// that divides only the OTHER side.
///
/// This test and its twin below exist because the differential oracle is
/// structurally blind here: on generated inputs the CRA reconstruction is
/// already correct, so the certificate never rejects, and deleting either half
/// of it changed nothing across 6,000 fuzz cases. A guard that never fires on
/// the corpus cannot be covered by the corpus. It is covered here by handing it
/// a candidate that is wrong in exactly one direction.
#[test]
fn the_modular_certificate_rejects_a_candidate_that_misses_the_first_side() {
    let mut c = Ctx::new();
    // u = x*(x+1), v = x*(x+2). The true gcd is x.
    let x = c.t(1, 1, 0, 0);
    let xp1 = {
        let a = c.t(1, 1, 0, 0);
        let b = c.c(1);
        c.add(&a, &b)
    };
    let xp2 = {
        let a = c.t(1, 1, 0, 0);
        let b = c.c(2);
        c.add(&a, &b)
    };
    let u = c.mul(&x, &xp1);
    let v = c.mul(&x, &xp2);
    // `x+2` divides v but NOT u: the `pp_u` leg must reject it.
    let bad = xp2.clone();
    assert!(
        c.m.certify_mod_gcd_candidate(&bad, &u, &v, &BigInt::one())
            .is_none(),
        "a candidate that does not divide the first input was accepted"
    );
    // The genuine gcd is accepted, so the test cannot pass vacuously.
    assert!(
        c.m.certify_mod_gcd_candidate(&x, &u, &v, &BigInt::one())
            .is_some(),
        "the true gcd must certify"
    );
}

/// The `pp_v` half of the certificate — the half a verifier proved could be
/// deleted without the oracle noticing.
#[test]
fn the_modular_certificate_rejects_a_candidate_that_misses_the_second_side() {
    let mut c = Ctx::new();
    let x = c.t(1, 1, 0, 0);
    let xp1 = {
        let a = c.t(1, 1, 0, 0);
        let b = c.c(1);
        c.add(&a, &b)
    };
    let xp2 = {
        let a = c.t(1, 1, 0, 0);
        let b = c.c(2);
        c.add(&a, &b)
    };
    let u = c.mul(&x, &xp1);
    let v = c.mul(&x, &xp2);
    // `x+1` divides u but NOT v: the `pp_v` leg must reject it.
    let bad = xp1.clone();
    assert!(
        c.m.certify_mod_gcd_candidate(&bad, &u, &v, &BigInt::one())
            .is_none(),
        "a candidate that does not divide the second input was accepted"
    );
}

/// The certificate carries the integer content back into the accepted answer.
#[test]
fn the_modular_certificate_restores_the_integer_content() {
    let mut c = Ctx::new();
    let x = c.t(1, 1, 0, 0);
    let xp1 = {
        let a = c.t(1, 1, 0, 0);
        let b = c.c(1);
        c.add(&a, &b)
    };
    let u = c.mul(&x, &xp1);
    let v = c.mul(&x, &x);
    let g =
        c.m.certify_mod_gcd_candidate(&x, &u, &v, &BigInt::from(6))
            .expect("the true gcd certifies");
    let expect = c.t(6, 1, 0, 0);
    assert_eq!(g, expect, "the accepted answer must carry d_a");
}

#[test]
fn every_declared_modulus_is_a_prime_below_2_pow_31() {
    fn is_prime(n: u64) -> bool {
        if n < 2 {
            return false;
        }
        let mut d = 2u64;
        while d * d <= n {
            if n % d == 0 {
                return false;
            }
            d += 1;
        }
        true
    }
    for &p in ZP_PRIMES.iter() {
        assert!(p < (1u64 << 31), "{p} must fit the u64 product bound");
        assert!(is_prime(p), "{p} is not prime");
    }
    let mut seen = ZP_PRIMES.to_vec();
    seen.sort_unstable();
    seen.dedup();
    assert_eq!(seen.len(), ZP_PRIMES.len(), "primes must be distinct");
}

#[test]
fn zp_inverse_is_a_genuine_inverse() {
    let zp = Zp::new(2_147_483_647);
    for a in [1u64, 2, 3, 1000, 123_456_789, 2_147_483_646] {
        let inv = zp.inv(a).expect("non-zero has an inverse");
        assert_eq!(zp.mul(a, inv), 1);
    }
    assert!(zp.inv(0).is_none());
}

#[test]
fn mod_gcd_fails_closed_rather_than_guessing() {
    let mut c = Ctx::new();
    let zero = c.m.zero();
    let p = c.t(3, 1, 1, 0);
    // Degenerate arguments are answered directly.
    assert_eq!(c.m.mod_gcd(&zero, &p).unwrap(), p);
    assert_eq!(c.m.mod_gcd(&p, &zero).unwrap(), p);
    let two = c.c(2);
    let six_p = c.t(6, 1, 1, 0);
    assert_eq!(c.m.mod_gcd(&two, &six_p).unwrap(), c.c(2));
    // Whatever it returns for a real pair, it must divide both.
    let q = c.t(5, 0, 1, 2);
    let u = c.mul(&p, &q);
    let v = c.mul(&q, &q);
    if let Some(g) = c.m.mod_gcd(&u, &v) {
        assert!(c.m.divides(&g, &u));
        assert!(c.m.divides(&g, &v));
    }
}

#[test]
fn coefficient_growth_of_the_two_gcds_is_measured_not_assumed() {
    // A deliberately ill-conditioned pair: a dense degree-6 cofactor pair over
    // a shared quadratic, where the PRS intermediates are known to swell.
    let mut c = Ctx::new();
    let g = {
        let a = c.t(1, 2, 0, 0);
        let b = c.t(-3, 1, 1, 0);
        let d = c.t(7, 0, 0, 1);
        let s = c.add(&a, &b);
        c.add(&s, &d)
    };
    let mut u = g.clone();
    let mut v = g.clone();
    for k in 1..=4i64 {
        let fa = c.t(k, 1, 0, 0);
        let fb = c.t(k + 1, 0, 1, 0);
        let fc = c.c(k * 3 - 1);
        let f = c.add(&fa, &fb);
        let f = c.add(&f, &fc);
        u = c.mul(&u, &f);
        let ha = c.t(k + 2, 1, 0, 0);
        let hb = c.t(-k, 0, 0, 1);
        let hc = c.c(k * 5 + 2);
        let h = c.add(&ha, &hb);
        let h = c.add(&h, &hc);
        v = c.mul(&v, &h);
    }
    let prs = c.m.gcd(&u, &v).unwrap();
    assert!(c.m.divides(&prs, &u) && c.m.divides(&prs, &v));
    let modular = c.m.mod_gcd(&u, &v);
    if let Some(mg) = modular {
        assert_eq!(mg, prs);
    }
    // The answer is small even though the inputs are not; that is the whole
    // point of the measurement in the oracle's `growth` subcommand.
    assert!(
        c.m.max_coeff_bits(&prs) <= c.m.max_coeff_bits(&u),
        "the gcd cannot be wider than the input it divides"
    );
}
