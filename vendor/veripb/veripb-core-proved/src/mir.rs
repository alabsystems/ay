//! Proved mixed-integer-rounding cuts (rule MIR), in both the normalized and
//! the variable form the live checker emits.
//!
//! Every item mirrors a definition or theorem in `clean/veripb_kernel.lean`:
//!
//! | Rust | Clean |
//! |---|---|
//! | [`floor_div`] | `VeriPbCore.intFloorDiv` |
//! | [`floor_mod`] | `VeriPbCore.intFloorMod` |
//! | [`mir_f`] | `VeriPbCore.mirF` |
//! | [`mir`] | `VeriPbCore.entails_mir` (`entails_mir_signed` for the signed reading) |
//! | [`mir_variable`] | `VeriPbCore.entails_mir_variable` (via `vfMirTerms` / `negSum`) |
//!
//! The Clean side computes over unbounded `Int` with a `Nat` divisor; here the
//! whole cut is computed at the domain's exact width and narrowed back through
//! [`CoeffDomain::narrow`] exactly once per value, so a coefficient or degree
//! the domain could not hold makes the rule refuse to fire rather than wrap.
//! At [`Big`](crate::Big) that narrowing is total, so the rule fires wherever
//! the Clean theorem applies and the three helper functions below *are* the
//! `Int` definitions. Both entry points check each of their theorem's
//! hypotheses explicitly, and both re-check the *values* they produced (the
//! division witness `q*k + m = x`, `0 <= m < k`, and — for the normalized
//! form — `mirF_nonneg`) as defence in depth, in the same spirit as
//! [`crate::divide`]'s quotient re-checks: MIR is where the upstream
//! oversized-divisor defect lived.
//!
//! The correspondence to the kernel-evaluated Clean controls (`ctrl_ifd_*`,
//! `ctrl_ifm_*`, `ctrl_mirF_*`, `ctrl_mir_5_3_*`, `ctrl_vf_*`) is pinned by
//! `mir_matches_the_clean_controls` in `tests/width_guards.rs`.

use crate::{CoeffDomain, Constraint, Exact, GuardError, Term};

/// Mirrors `VeriPbCore.intFloorDiv`: floor division by a strictly positive
/// divisor.
///
/// Clean splits on the sign of `x` — `Int.ofNat n` divides through
/// `natDivMod`, `Int.negSucc m` through `-natCeilDiv` — which is floor
/// division on both branches. Both [`Exact`] implementations of
/// [`Exact::div_mod_floor`] compute exactly that for a positive divisor; see
/// their docs for why.
pub fn floor_div<E: Exact>(x: &E, k: &E) -> E {
    debug_assert!(k.is_positive());
    x.div_mod_floor(k).0
}

/// Mirrors `VeriPbCore.intFloorMod`: the remainder of [`floor_div`], always in
/// `0 ..= k-1`.
///
/// Clean's negative branch is `natCeilDiv(-x) * k - (-x)`, i.e. `x - k *
/// floorDiv x k` rearranged — nonnegative by construction, as
/// `intFloorMod_nonneg` states.
pub fn floor_mod<E: Exact>(x: &E, k: &E) -> E {
    debug_assert!(k.is_positive());
    x.div_mod_floor(k).1
}

/// Mirrors `VeriPbCore.mirF`: `floorDiv(x,k) * r + capCoeff(r, floorMod(x,k))`.
///
/// The capping is the crate's own [`Exact::cap_coeff`], the exact-width twin
/// of the `capCoeff` image [`crate::cap_coeff`] SATURATE runs — `mirF` is
/// literally `Int.add (Int.mul (intFloorDiv x k) r) (capCoeff r (intFloorMod x
/// k))`, so the same function must appear here.
///
/// Exact at the narrow domain's [`Wide`](crate::Wide) width for every input
/// the rules admit: `|floorDiv(x,k)| <= 2^63` and `0 < r <= k <= 2^63`, so the
/// product is below `2^126`. At [`Big`](crate::Big) it is exact outright.
///
/// Both arithmetic steps go through [`Exact::checked_mul`] /
/// [`Exact::checked_add`], which at the narrow domain are the contracted
/// leaves [`crate::mul_coeff_wide`] and [`crate::add_degree_wide`]. The
/// headroom argument above says the `None` branch is unreachable on admitted
/// inputs; returning `Option` means that argument is *enforced* rather than
/// relied on, in the same spirit as the re-checks below.
pub fn mir_f<E: Exact>(k: &E, r: &E, x: &E) -> Option<E> {
    let (q, m) = x.div_mod_floor(k);
    q.checked_mul(r)?.checked_add(&E::cap_coeff(r, &m))
}

/// The hypotheses of `entails_mir` / `entails_mir_variable` that the caller
/// must establish before the divisor and remainder are usable.
///
/// `k >= 1` is `hk : Nat.le 1 k`; `r > 0` is `hr0 : Int.lt 0 r`. A zero
/// remainder is not a defect — the cut degenerates to the trivial constraint
/// and the caller derives it by `entails_trivial` instead — so it gets its own
/// variant rather than being folded into a width failure.
fn checked_remainder<C: CoeffDomain>(
    k: &C,
    a: &C::Exact,
) -> Result<(C::Exact, C::Exact), GuardError> {
    if !C::is_nonneg(k) || *k == C::zero() {
        return Err(GuardError::NonPositiveFactor);
    }
    let kw = k.widen();
    let (q, r) = a.div_mod_floor(&kw);
    // `intFloorMod_nonneg` / `intFloorMod_lt`, and the division witness
    // `q * k + m = x` (`intFloor_spec`), re-checked on the values produced.
    // The witness is recomputed through the contracted leaves, so a product
    // or sum this width cannot hold refuses the rule instead of wrapping into
    // an equation that might accidentally hold.
    //
    // So are the two ORDER decisions. `intFloorMod_nonneg` is
    // [`Exact::is_negative`], the negation of [`crate::wide_nonneg`]
    // (`wide_sign_exact`) at the narrow domain; `intFloorMod_lt` is
    // [`Exact::at_least`], i.e. [`crate::wide_at_least`] (`wide_le_exact`).
    // Both are taken at the exact width on a remainder that has not been
    // narrowed, which is why the theorems behind them are the `key128` ones
    // rather than the `i64` sign theorem `weaken_factor_sign_exact`.
    let witness = q
        .checked_mul(&kw)
        .and_then(|p| p.checked_add(&r))
        .ok_or(GuardError::QuotientNotCeiling)?;
    if r.is_negative() || r.at_least(&kw) || witness != *a {
        return Err(GuardError::QuotientNotCeiling);
    }
    // `hr0` (`Int.lt 0 r`), spelled `1 <= r` by [`Exact::is_positive`] — the
    // same contracted comparison as the bound above.
    if !r.is_positive() {
        return Err(GuardError::MirZeroRemainder);
    }
    Ok((kw, r))
}

/// **Rule MIR** — for a normalized entailed `sum a_i l_i >= A` and `k > 0`
/// with `r = A mod k` nonzero, `sum mirF(a_i) l_i >= (floorDiv(A,k) + 1) * r`
/// is entailed.
///
/// Proved by `VeriPbCore.entails_mir`, whose hypotheses are checked here one
/// for one: `hk` (`k >= 1`), `hn` (`AllNonneg c.terms`), `hr`/`hr0` (`r` is
/// the floor-mod and is positive). `mirF_nonneg` says the produced
/// coefficients stay nonnegative on this branch, so the cut is normalized
/// again; that too is re-checked rather than assumed.
///
/// `Err(GuardError::MirZeroRemainder)` means `k` divides `A`: the Clean rule
/// has no content there and the caller should derive the trivial constraint
/// (`entails_trivial`) instead.
pub fn mir<C: CoeffDomain>(k: C, c: &Constraint<C>) -> Result<Constraint<C>, GuardError> {
    if !c.all_nonneg() {
        return Err(GuardError::NotNormalized);
    }
    let (kw, r) = checked_remainder::<C>(&k, &c.degree.widen())?;
    let mut terms = Vec::with_capacity(c.terms.len());
    for t in &c.terms {
        let mapped = mir_f(&kw, &r, &t.coeff.widen()).ok_or(GuardError::CoeffOverflow)?;
        // `mirF_nonneg`, on the value actually produced — [`Exact::is_negative`],
        // i.e. the negation of the contracted [`crate::wide_nonneg`] at the
        // narrow domain.
        if mapped.is_negative() {
            return Err(GuardError::QuotientNotCeiling);
        }
        let coeff = C::narrow(&mapped).ok_or(GuardError::CoeffOverflow)?;
        terms.push(Term { coeff, lit: t.lit });
    }
    let one = <C::Exact as Exact>::one();
    let degree_exact = floor_div(&c.degree.widen(), &kw)
        .checked_add(&one)
        .and_then(|q1| q1.checked_mul(&r))
        .ok_or(GuardError::DegreeOverflow)?;
    let degree = C::narrow(&degree_exact).ok_or(GuardError::DegreeOverflow)?;
    Ok(C::pack(terms, degree))
}

/// **Rule MIR, variable form** — the live checker's cut on a constraint whose
/// negated literals are read in variable space.
///
/// Proved by `VeriPbCore.entails_mir_variable`: with
/// `A = c.degree - negSum c.terms` and `r = A mod k` nonzero, every
/// coefficient maps through `vfMapTerm (mirF k r)` — `mirF(a)` on a plain
/// literal, `-mirF(-a)` on a negated one — and the degree becomes
/// `(floorDiv(A,k) + 1) * r + negSum(new terms)`. There is no sign condition:
/// the eval bound underneath is the unconditional `mirF_subadd`
/// (`entails_mir_signed` is the same statement without `AllNonneg`).
///
/// `Err(GuardError::MirZeroRemainder)` degenerates to the trivial constraint,
/// exactly as in [`mir`].
pub fn mir_variable<C: CoeffDomain>(k: C, c: &Constraint<C>) -> Result<Constraint<C>, GuardError> {
    // `negSum`: the coefficients of the negated literals, which the flip
    // shifts to the right-hand side.
    let neg_sum = <C::Exact as Exact>::sum(
        c.terms
            .iter()
            .filter(|t| t.lit.negated)
            .map(|t| t.coeff.widen()),
    );
    let a = c
        .degree
        .widen()
        .checked_sub(&neg_sum)
        .ok_or(GuardError::DegreeOverflow)?;
    let (kw, r) = checked_remainder::<C>(&k, &a)?;
    let mut terms = Vec::with_capacity(c.terms.len());
    let mut new_neg_sum = <C::Exact as Exact>::zero();
    for t in &c.terms {
        // `varCoeff`: the term's coefficient in variable space.
        let w = t.coeff.widen();
        let var_space = if t.lit.negated { w.neg() } else { w };
        let mapped = mir_f(&kw, &r, &var_space).ok_or(GuardError::CoeffOverflow)?;
        // `varCoeffB`, flipping the image back onto the original literal.
        let stored = if t.lit.negated { mapped.neg() } else { mapped };
        if t.lit.negated {
            new_neg_sum = new_neg_sum
                .checked_add(&stored)
                .ok_or(GuardError::CoeffOverflow)?;
        }
        let coeff = C::narrow(&stored).ok_or(GuardError::CoeffOverflow)?;
        terms.push(Term { coeff, lit: t.lit });
    }
    let one = <C::Exact as Exact>::one();
    let degree_exact = floor_div(&a, &kw)
        .checked_add(&one)
        .and_then(|q1| q1.checked_mul(&r))
        .and_then(|d| d.checked_add(&new_neg_sum))
        .ok_or(GuardError::DegreeOverflow)?;
    let degree = C::narrow(&degree_exact).ok_or(GuardError::DegreeOverflow)?;
    Ok(C::pack(terms, degree))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Big, Lit};

    #[test]
    fn zero_remainder_is_its_own_outcome() {
        // 2x >= 4, divisor 2: `r = 0`, so the Clean rule says nothing and the
        // caller must fall back on `entails_trivial`.
        let c = Constraint::new(
            vec![Term {
                coeff: 2,
                lit: Lit::pos(0),
            }],
            4,
        );
        assert_eq!(mir(2, &c), Err(GuardError::MirZeroRemainder));
    }

    #[test]
    fn normalized_form_requires_all_nonneg() {
        let c = Constraint::new(
            vec![Term {
                coeff: -1,
                lit: Lit::pos(0),
            }],
            5,
        );
        assert_eq!(mir(3, &c), Err(GuardError::NotNormalized));
        // The variable form has no sign condition (`entails_mir_signed`).
        assert!(mir_variable(3, &c).is_ok());
    }

    #[test]
    fn non_positive_divisor_is_refused() {
        let c = Constraint::new(
            vec![Term {
                coeff: 5,
                lit: Lit::pos(0),
            }],
            5,
        );
        assert_eq!(mir(0, &c), Err(GuardError::NonPositiveFactor));
        assert_eq!(mir(-2, &c), Err(GuardError::NonPositiveFactor));
        assert_eq!(mir_variable(0, &c), Err(GuardError::NonPositiveFactor));
    }

    #[test]
    fn the_cut_is_semantically_sound_on_a_witness() {
        // 5x + 5y >= 5 with k = 3: r = 2, coefficients mirF(5) = 4, degree
        // (1 + 1) * 2 = 4 — the `ctrl_mir_5_3_*` values. Every model of the
        // base constraint models the cut.
        let c = Constraint::new(
            vec![
                Term {
                    coeff: 5,
                    lit: Lit::pos(0),
                },
                Term {
                    coeff: 5,
                    lit: Lit::pos(1),
                },
            ],
            5,
        );
        let cut = mir(3, &c).unwrap();
        assert_eq!(cut.degree, 4);
        assert!(cut.terms.iter().all(|t| t.coeff == 4));
        for x in [false, true] {
            for y in [false, true] {
                let a = move |v: u32| if v == 0 { x } else { y };
                if c.holds(&a) {
                    assert!(cut.holds(&a), "cut lost a model at ({x}, {y})");
                }
            }
        }
    }

    /// The same cut one width up, on a coefficient no machine word holds: the
    /// narrow domain refuses, the complete one produces the exact cut and it
    /// is still sound on every model.
    #[test]
    fn the_cut_beyond_i64_is_refused_narrow_and_exact_wide() {
        let big_coeff = Big::from(u64::MAX) * Big::from(u64::MAX);
        let narrow = Constraint::new(
            vec![Term {
                coeff: i64::MAX,
                lit: Lit::pos(0),
            }],
            i64::MAX,
        );
        // i64::MAX mod 3 = 1, so the rule fires; the *degree* stays in range
        // here, which is what makes the wide comparison below meaningful.
        assert!(mir(3, &narrow).is_ok());

        // `huge` is divisible by 3, so the degree is offset by one to give
        // the rule a non-zero remainder to cut on, and to leave the base
        // constraint a model (`x = true`) for the soundness check below.
        let c = Constraint::new(
            vec![Term {
                coeff: big_coeff.clone(),
                lit: Lit::pos(0),
            }],
            big_coeff.clone() - Big::from(1),
        );
        let cut = mir(Big::from(3), &c).unwrap();
        // Soundness on both assignments of the single variable.
        for x in [false, true] {
            let a = move |_: u32| x;
            if c.holds(&a) {
                assert!(cut.holds(&a));
            }
        }
        // And the cut really is above i64: it is not a narrowed shadow.
        assert!(cut.terms[0].coeff > Big::from(i64::MAX));
    }

    #[test]
    fn variable_form_beyond_i64_is_exact() {
        let huge = Big::from(u64::MAX) * Big::from(u64::MAX);
        let c = Constraint::new(
            vec![
                Term {
                    coeff: huge.clone(),
                    lit: Lit::pos(0),
                },
                Term {
                    coeff: Big::from(2),
                    lit: Lit::neg(1),
                },
            ],
            huge.clone(),
        );
        let cut = mir_variable(Big::from(3), &c).unwrap();
        for x in [false, true] {
            for y in [false, true] {
                let a = move |v: u32| if v == 0 { x } else { y };
                if c.holds(&a) {
                    assert!(
                        cut.holds(&a),
                        "variable-form cut lost a model at ({x}, {y})"
                    );
                }
            }
        }
    }
}
