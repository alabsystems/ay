// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// ===========================================================================
// The sparse multivariate polynomial manager (`crate::polymanager`)
// ===========================================================================

/// Facade over [`crate::polymanager::PolyManager`].
///
/// The manager owns the interned monomial table, so every polynomial handed
/// out by this type belongs to the manager that produced it and the oracle
/// keeps exactly one alive per case. Handles are opaque [`OMgrPoly`] values;
/// the oracle never sees a `MonoId`, which is what keeps a manager mix-up
/// impossible from outside the crate.
pub struct OPolyMgr(polymanager::PolyManager);

/// A polynomial belonging to an [`OPolyMgr`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OMgrPoly(polymanager::Poly);

/// Why one `mod_gcd` call declined, as counted inside the manager.
///
/// A decline is always SAFE (`PolyManager::gcd` falls back to the subresultant
/// PRS) but it is never free, so raising the certification rate needs to know
/// WHICH mechanism gave up. This is the read-only view of those counters.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OModGcdDiag(polymanager::ModGcdDiag);

impl OModGcdDiag {
    /// The single dominant cause, as a stable label suitable for a histogram
    /// key. `"certified"` when the call did not decline.
    #[must_use]
    pub fn primary(&self) -> &'static str {
        self.0.primary()
    }

    /// Whether the call ended in a certified answer.
    #[must_use]
    pub fn certified(&self) -> bool {
        self.0.certified()
    }

    /// Answers returned by a shortcut instead of by the certificate: a zero
    /// input, a constant input, or a unit modular image.
    #[must_use]
    pub fn shortcuts(&self) -> u32 {
        self.0.shortcut_zero + self.0.shortcut_const + self.0.shortcut_unit_image
    }

    /// Primes entered, and primes rejected before the recursion ran.
    #[must_use]
    pub fn primes_used(&self) -> u32 {
        self.0.primes_used
    }
    /// Primes rejected because a coefficient of `u` or `v` vanished mod `p`.
    #[must_use]
    pub fn prime_bad_coeff(&self) -> u32 {
        self.0.prime_bad_coeff
    }
    /// Primes rejected because the imposed leading coefficient vanished mod `p`.
    #[must_use]
    pub fn prime_bad_lcg(&self) -> u32 {
        self.0.prime_bad_lcg
    }
    /// Primes whose `Z_p` Brown recursion declined.
    #[must_use]
    pub fn prime_rec_declined(&self) -> u32 {
        self.0.prime_rec_declined
    }
    /// CRA rounds whose candidate failed the leading-coefficient gate.
    #[must_use]
    pub fn lc_gate_rejected(&self) -> u32 {
        self.0.lc_gate_rejected
    }
    /// Times the EXACT certificate rejected on the `u` leg.
    #[must_use]
    pub fn cert_reject_u(&self) -> u32 {
        self.0.cert_reject_u
    }
    /// Times the EXACT certificate rejected on the `v` leg.
    #[must_use]
    pub fn cert_reject_v(&self) -> u32 {
        self.0.cert_reject_v
    }
    /// Times the EXACT certificate accepted.
    #[must_use]
    pub fn cert_accepted(&self) -> u32 {
        self.0.cert_accepted
    }
    /// CRA steps that could not be combined.
    #[must_use]
    pub fn cra_failed(&self) -> u32 {
        self.0.cra_failed
    }
    /// Evaluation points the level below could not answer for.
    #[must_use]
    pub fn rec_inner_declined(&self) -> u32 {
        self.0.rec_inner_declined
    }
    /// Levels that ran out of evaluation-point budget.
    #[must_use]
    pub fn rec_budget_exhausted(&self) -> u32 {
        self.0.rec_budget_exhausted
    }
    /// Base-case Euclid refusals.
    #[must_use]
    pub fn rec_base_failed(&self) -> u32 {
        self.0.rec_base_failed
    }
    /// Content / primitive-part refusals inside the recursion.
    #[must_use]
    pub fn rec_content_failed(&self) -> u32 {
        self.0.rec_content_failed
    }
    /// Leading-coefficient GCD refusals inside the recursion.
    #[must_use]
    pub fn rec_lcgcd_failed(&self) -> u32 {
        self.0.rec_lcgcd_failed
    }
    /// Points where the `lc_H == lc_g` gate had not stabilized yet.
    #[must_use]
    pub fn rec_lch_mismatch(&self) -> u32 {
        self.0.rec_lch_mismatch
    }
    /// Points where the trial exact division rejected the interpolant.
    #[must_use]
    pub fn rec_trialdiv_reject(&self) -> u32 {
        self.0.rec_trialdiv_reject
    }
    /// Points discarded as unlucky (image leading monomial too large).
    #[must_use]
    pub fn rec_unlucky_degree(&self) -> u32 {
        self.0.rec_unlucky_degree
    }
    /// Points discarded because the imposed leading coefficient vanished there.
    #[must_use]
    pub fn rec_point_lcg_zero(&self) -> u32 {
        self.0.rec_point_lcg_zero
    }
    /// Evaluation points consumed, across every level and prime.
    #[must_use]
    pub fn rec_points_tried(&self) -> u32 {
        self.0.rec_points_tried
    }
    /// Images that could not be made glex-monic (they were zero).
    #[must_use]
    pub fn rec_monic_failed(&self) -> u32 {
        self.0.rec_monic_failed
    }
    /// Levels that used up every point of the field.
    #[must_use]
    pub fn rec_field_exhausted(&self) -> u32 {
        self.0.rec_field_exhausted
    }
    /// Newton steps that could not be extended.
    #[must_use]
    pub fn rec_newton_failed(&self) -> u32 {
        self.0.rec_newton_failed
    }
    /// Times the accumulated Newton form was discarded for a smaller image.
    #[must_use]
    pub fn rec_reset_smaller(&self) -> u32 {
        self.0.rec_reset_smaller
    }
    /// Largest number of interpolation points accumulated at one level.
    #[must_use]
    pub fn rec_max_points_at_level(&self) -> u32 {
        self.0.rec_max_points_at_level
    }
    /// Largest degree bound any level interpolated against.
    #[must_use]
    pub fn rec_max_deg_bound(&self) -> u32 {
        self.0.rec_max_deg_bound
    }
}

/// The result of a pseudo-division: `lc(q, x)^d * p == quot * q + rem`.
pub struct OPseudoDiv {
    /// The power of `lc(q, x)` carried by the identity.
    pub d: u32,
    /// The pseudo-quotient.
    pub quot: OMgrPoly,
    /// The pseudo-remainder.
    pub rem: OMgrPoly,
}

impl Default for OPolyMgr {
    fn default() -> Self {
        Self::new()
    }
}

impl OPolyMgr {
    /// A fresh manager.
    #[must_use]
    pub fn new() -> Self {
        Self(polymanager::PolyManager::new())
    }

    /// Build a polynomial from `(variable/exponent pairs, coefficient)` terms.
    pub fn mk(&mut self, terms: &[(Vec<(u32, u32)>, BigInt)]) -> OMgrPoly {
        OMgrPoly(self.0.mk_from_pairs(terms))
    }

    /// A constant polynomial.
    #[must_use]
    pub fn constant(&self, c: BigInt) -> OMgrPoly {
        OMgrPoly(self.0.mk_const(c))
    }

    /// The zero polynomial.
    #[must_use]
    pub fn zero(&self) -> OMgrPoly {
        OMgrPoly(self.0.zero())
    }

    /// Is this the zero polynomial?
    #[must_use]
    pub fn is_zero(&self, p: &OMgrPoly) -> bool {
        p.0.is_zero()
    }

    /// Is this polynomial free of variables?
    #[must_use]
    pub fn is_const(&self, p: &OMgrPoly) -> bool {
        self.0.is_const(&p.0)
    }

    /// Number of non-zero terms.
    #[must_use]
    pub fn len(&self, p: &OMgrPoly) -> usize {
        p.0.len()
    }

    /// Whether the polynomial has no terms at all.
    #[must_use]
    pub fn is_empty(&self, p: &OMgrPoly) -> bool {
        p.0.len() == 0
    }

    /// `deg_x(p)`.
    #[must_use]
    pub fn degree(&self, p: &OMgrPoly, x: u32) -> u32 {
        self.0.degree(&p.0, x)
    }

    /// Total degree.
    #[must_use]
    pub fn total_degree(&self, p: &OMgrPoly) -> u32 {
        self.0.total_degree(&p.0)
    }

    /// The variables occurring in `p`, ascending.
    #[must_use]
    pub fn vars(&self, p: &OMgrPoly) -> Vec<u32> {
        self.0.vars(&p.0)
    }

    /// The largest variable, or `None` for a constant.
    #[must_use]
    pub fn max_var(&self, p: &OMgrPoly) -> Option<u32> {
        self.0.max_var(&p.0)
    }

    /// Widest coefficient, in bits. Measurement only.
    #[must_use]
    pub fn max_coeff_bits(&self, p: &OMgrPoly) -> u64 {
        self.0.max_coeff_bits(&p.0)
    }

    /// How many distinct monomials the manager has interned. Measurement only.
    #[must_use]
    pub fn interned(&self) -> usize {
        self.0.interned()
    }

    /// The canonical term list as `(exponent pairs, coefficient)`, descending
    /// under the manager's monomial order. This is the ONLY way the oracle can
    /// see inside a `Poly`, and it is how the canonical-form invariants are
    /// checked from outside.
    #[must_use]
    pub fn terms(&self, p: &OMgrPoly) -> Vec<(Vec<(u32, u32)>, BigInt)> {
        p.0.terms()
            .iter()
            .map(|&(m, ref c)| (self.0.mono_pows(m).to_vec(), c.clone()))
            .collect()
    }

    /// Sum.
    #[must_use]
    pub fn add(&self, a: &OMgrPoly, b: &OMgrPoly) -> OMgrPoly {
        OMgrPoly(self.0.add(&a.0, &b.0))
    }

    /// Difference.
    #[must_use]
    pub fn sub(&self, a: &OMgrPoly, b: &OMgrPoly) -> OMgrPoly {
        OMgrPoly(self.0.sub(&a.0, &b.0))
    }

    /// Additive inverse.
    #[must_use]
    pub fn neg(&self, a: &OMgrPoly) -> OMgrPoly {
        OMgrPoly(self.0.neg(&a.0))
    }

    /// Product.
    pub fn mul(&mut self, a: &OMgrPoly, b: &OMgrPoly) -> OMgrPoly {
        OMgrPoly(self.0.mul(&a.0, &b.0))
    }

    /// `a^k`.
    pub fn pow(&mut self, a: &OMgrPoly, k: u32) -> OMgrPoly {
        OMgrPoly(self.0.pow(&a.0, k))
    }

    /// Multiply by an integer.
    #[must_use]
    pub fn mul_int(&self, a: &OMgrPoly, c: &BigInt) -> OMgrPoly {
        OMgrPoly(self.0.mul_int(&a.0, c))
    }

    /// `dp/dx`.
    pub fn derivative(&mut self, p: &OMgrPoly, x: u32) -> OMgrPoly {
        OMgrPoly(self.0.derivative(&p.0, x))
    }

    /// Substitute an integer for `x`.
    pub fn eval_var(&mut self, p: &OMgrPoly, x: u32, a: &BigInt) -> OMgrPoly {
        OMgrPoly(self.0.eval_var(&p.0, x, a))
    }

    /// The coefficient of `x^k`.
    pub fn coeff(&mut self, p: &OMgrPoly, x: u32, k: u32) -> OMgrPoly {
        OMgrPoly(self.0.coeff(&p.0, x, k))
    }

    /// The recursive view in `x`.
    pub fn x_coeffs(&mut self, p: &OMgrPoly, x: u32) -> Vec<OMgrPoly> {
        self.0.x_coeffs(&p.0, x).into_iter().map(OMgrPoly).collect()
    }

    /// Rebuild from a recursive view in `x`.
    pub fn from_x_coeffs(&mut self, x: u32, cs: &[OMgrPoly]) -> OMgrPoly {
        let raw: Vec<polymanager::Poly> = cs.iter().map(|c| c.0.clone()).collect();
        OMgrPoly(self.0.from_x_coeffs(x, &raw))
    }

    /// `lc(p, x)`.
    pub fn lc(&mut self, p: &OMgrPoly, x: u32) -> OMgrPoly {
        OMgrPoly(self.0.lc(&p.0, x))
    }

    /// Exact division, `None` when it does not divide.
    pub fn exact_div(&mut self, a: &OMgrPoly, b: &OMgrPoly) -> Option<OMgrPoly> {
        self.0.exact_div(&a.0, &b.0).map(OMgrPoly)
    }

    /// Whether `b` divides `a`.
    pub fn divides(&mut self, b: &OMgrPoly, a: &OMgrPoly) -> bool {
        self.0.divides(&b.0, &a.0)
    }

    /// Pseudo-division. `exact` selects z3's `Exact_d` mode.
    pub fn pseudo_division(
        &mut self,
        p: &OMgrPoly,
        q: &OMgrPoly,
        x: u32,
        exact: bool,
    ) -> Option<OPseudoDiv> {
        let mode = if exact {
            polymanager::PseudoMode::Exact
        } else {
            polymanager::PseudoMode::Loose
        };
        self.0
            .pseudo_division(&p.0, &q.0, x, mode)
            .map(|r| OPseudoDiv {
                d: r.d,
                quot: OMgrPoly(r.quot),
                rem: OMgrPoly(r.rem),
            })
    }

    /// The integer content / content / primitive-part split with respect to
    /// `x`, as `(i, c, pp)` with `p == i * c * pp`.
    pub fn iccp(&mut self, p: &OMgrPoly, x: u32) -> Option<(BigInt, OMgrPoly, OMgrPoly)> {
        self.0
            .iccp(&p.0, x)
            .map(|r| (r.i, OMgrPoly(r.c), OMgrPoly(r.pp)))
    }

    /// The PRS GCD.
    /// The subresultant PRS answer with the modular fast path disabled all the
    /// way down. Every check that treats the PRS as an INDEPENDENT second
    /// opinion on `mod_gcd`, and every cost measurement reporting a PRS column,
    /// must use this rather than [`OPolyMgr::gcd`].
    pub fn gcd_via_prs(&mut self, a: &OMgrPoly, b: &OMgrPoly) -> Option<OMgrPoly> {
        self.0.gcd_via_prs(&a.0, &b.0).map(OMgrPoly)
    }

    /// The certified polynomial GCD, using the manager's default strategy.
    pub fn gcd(&mut self, a: &OMgrPoly, b: &OMgrPoly) -> Option<OMgrPoly> {
        self.0.gcd(&a.0, &b.0).map(OMgrPoly)
    }

    /// The modular (Brown) GCD; `None` when it could not certify a candidate.
    pub fn mod_gcd(&mut self, a: &OMgrPoly, b: &OMgrPoly) -> Option<OMgrPoly> {
        self.0.mod_gcd(&a.0, &b.0).map(OMgrPoly)
    }

    /// The modular GCD together with the DECLINE DIAGNOSIS of that call.
    ///
    /// The counters are written by `mod_gcd` and never read by it, so calling
    /// this instead of [`OPolyMgr::mod_gcd`] cannot change the answer — an
    /// invariant the `pm-mod-gcd-diag` oracle check asserts on every case.
    pub fn mod_gcd_diag(&mut self, a: &OMgrPoly, b: &OMgrPoly) -> (Option<OMgrPoly>, OModGcdDiag) {
        let r = self.0.mod_gcd(&a.0, &b.0).map(OMgrPoly);
        (r, OModGcdDiag(self.0.mod_gcd_diag()))
    }

    /// The square-free part with respect to `x`.
    pub fn square_free_in(&mut self, p: &OMgrPoly, x: u32) -> Option<OMgrPoly> {
        self.0.square_free_in(&p.0, x).map(OMgrPoly)
    }

    /// The whole-polynomial square-free part.
    pub fn square_free(&mut self, p: &OMgrPoly) -> Option<OMgrPoly> {
        self.0.square_free(&p.0).map(OMgrPoly)
    }

    /// Whether `p` is already square-free with respect to `x`.
    pub fn is_square_free_in(&mut self, p: &OMgrPoly, x: u32) -> Option<bool> {
        self.0.is_square_free_in(&p.0, x)
    }

    /// The positive GCD of the coefficients (`0` for the zero polynomial).
    ///
    /// Exposed for the one invariant that pins the SCALAR half of
    /// `square_free`: a dropped integer content is invisible to divisibility,
    /// to root sets and to square-freeness, and was found live by a verifier.
    #[must_use]
    pub fn int_content(&self, p: &OMgrPoly) -> BigInt {
        self.0.int_content(&p.0)
    }

    /// Specialize every variable except `x` to the given integers and read the
    /// result out as a DENSE low-to-high coefficient list in `x`.
    ///
    /// `None` when the specialization leaves a variable other than `x`
    /// standing, which would make the univariate reading a lie. This is the
    /// bridge every z3-backed check crosses: it turns a multivariate answer
    /// into something z3's univariate `Z3_algebraic_*` API can be asked about.
    pub fn specialize(
        &mut self,
        p: &OMgrPoly,
        x: u32,
        point: &[(u32, BigInt)],
    ) -> Option<Vec<BigInt>> {
        let mut cur = p.0.clone();
        for (v, val) in point {
            if *v == x {
                continue;
            }
            cur = self.0.eval_var(&cur, *v, val);
        }
        for v in self.0.vars(&cur) {
            if v != x {
                return None;
            }
        }
        if cur.is_zero() {
            return Some(Vec::new());
        }
        let d = self.0.degree(&cur, x);
        let mut out = vec![BigInt::from(0); d as usize + 1];
        for cs in self.0.x_coeffs(&cur, x).iter().enumerate() {
            let (k, c) = cs;
            out[k] = self.0.const_value(c)?;
        }
        while out.last().is_some_and(num_traits::Zero::is_zero) {
            out.pop();
        }
        Some(out)
    }
}
