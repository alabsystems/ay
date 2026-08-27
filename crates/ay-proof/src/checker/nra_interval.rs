// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict semantic validation for `TheoryLemmaKind::NraIntervalUnsat`.
//!
//! # The obligation
//!
//! An `NraIntervalUnsat` lemma claims: "the NEGATION of this clause is a
//! conjunction of polynomial sign constraints over Real/Int-sorted terms,
//! at least one monomial is genuinely nonlinear, and bounded exact-rational
//! interval propagation refutes the conjunction". The checker re-derives the
//! whole refutation with ITS OWN kernel — nothing about the solver's phase,
//! run, or reasoning is referenced or trusted; the kind carries no payload,
//! so there is nothing to forge.
//!
//! # The kernel (HC4-style contract/evaluate)
//!
//! Round-robin over the constraints, bounded by [`MAX_INTERVAL_PASSES`]:
//!
//! 1. FORWARD-evaluate each constraint polynomial over the current variable
//!    box with exact rational interval arithmetic (open/closed endpoints
//!    tracked; when uncertain an endpoint is CLOSED, which enlarges the set
//!    and is always sound).
//! 2. REFUTE when the computed interval wholly violates the relation. The
//!    computed interval over-approximates the true range, so a violated
//!    superset transfers the violation to the true range — over-approximation
//!    can only cause MISSED refutations, never false ones.
//! 3. BACKWARD-narrow (HC4 revise): each monomial is bounded by the
//!    rel-implied interval of the polynomial minus the interval sum of the
//!    other monomials; each variable power is narrowed by exact interval
//!    division when the cofactor excludes 0, and the variable by outward
//!    rational root bounds (even-power ray splits are SKIPPED — keeping the
//!    hull is sound). Every narrowing intersects a domain with an
//!    over-approximation of the constraint's feasible projection.
//! 4. REFUTE when any domain or narrowing target becomes empty: the box
//!    always contains the solution set, so an empty box proves infeasibility.
//!
//! Fixpoint or pass-cap without refutation, any unsupported shape, any
//! budget trip: `Err` — the funnel publishes `unknown`, byte-identical to
//! the pre-existing `Generic` rejection. Fail-closed everywhere.

use ay_core::{ProofId, TermId, TermStore};
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use std::collections::BTreeMap;

use super::nra_poly::{
    extract_constraints, rat_nth_root_bounds, Bnd, Constraint, Ival, Monomial, Rel, WorkMeter,
    MAX_ENDPOINT_BITS, MAX_INTERVAL_PASSES, MAX_INTERVAL_VARS,
};
use super::ProofCheckError;

/// Whether the negation of the clause is a conjunction of polynomial sign
/// constraints over Real/Int terms that the checker's OWN bounded
/// exact-rational interval propagation refutes.
///
/// This is the EXACT precondition of `validate_nra_interval_unsat`, so the
/// proof classifier in `ay-dpll` can only assign the kind to lemmas strict
/// mode will then accept — no classifier/checker drift. All decision logic
/// lives ONLY in this module and the shared `nra_poly` kernel.
#[must_use]
pub fn recognize_nra_interval_unsat(terms: &TermStore, clause: &[TermId]) -> bool {
    decide_nra_interval_unsat(terms, clause).is_ok()
}

/// Validate a `TheoryLemmaKind::NraIntervalUnsat` lemma in strict mode.
pub(crate) fn validate_nra_interval_unsat(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    decide_nra_interval_unsat(terms, clause).map_err(|reason| ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: format!("nra_interval_unsat: {reason}"),
    })
}

/// The single deciding routine both the recognizer and validator call
/// (recognize == validate-success by construction). Deterministic:
/// `BTreeMap`-only iteration, fresh work meter per call.
fn decide_nra_interval_unsat(terms: &TermStore, clause: &[TermId]) -> Result<(), String> {
    let mut meter = WorkMeter::new();
    let ext = extract_constraints(terms, clause, &mut meter)?;
    if !ext.has_nonlinear {
        return Err(
            "no monomial of total degree >= 2; linear conflicts stay in the LRA/LIA lanes"
                .to_string(),
        );
    }
    if ext.const_refuted {
        // A constant conjunct of the negated clause is FALSE: the conjunction
        // is infeasible outright and the clause is valid.
        return Ok(());
    }
    if ext.constraints.is_empty() {
        return Err("no surviving constraints; an empty conjunction is unrefutable".to_string());
    }
    if ext.vars.len() > MAX_INTERVAL_VARS {
        return Err(format!(
            "{} variables exceed the interval kernel cap {MAX_INTERVAL_VARS}",
            ext.vars.len()
        ));
    }

    let mut dom: BTreeMap<TermId, Ival> = ext.vars.iter().map(|&v| (v, Ival::full())).collect();

    for _pass in 0..MAX_INTERVAL_PASSES {
        let before = dom.clone();
        for c in &ext.constraints {
            if revise_constraint(c, &mut dom, &mut meter)? {
                // The box (which always contains the solution set of the
                // negated clause) is proven to admit no solution.
                return Ok(());
            }
        }
        // Endpoint bit-size guard: backward narrowing can grow exact
        // rational endpoints multiplicatively pass over pass; refuse instead
        // of carrying huge-integer endpoints into another pass (the work
        // meter separately bounds the arithmetic inside a pass).
        if dom.values().any(|iv| iv.bits() > MAX_ENDPOINT_BITS) {
            return Err("interval endpoint bit cap exceeded".to_string());
        }
        if dom == before {
            return Err("interval propagation reached a fixpoint without refutation".to_string());
        }
    }
    Err("interval propagation pass cap reached without refutation".to_string())
}

/// The rel-implied interval the polynomial must lie in for the constraint to
/// hold (`None` for `!=`, which admits no interval representation).
fn rel_target(rel: Rel) -> Option<Ival> {
    match rel {
        Rel::Eq => Some(Ival::point(BigRational::zero())),
        Rel::Gt => Some(Ival {
            lo: Bnd::open(BigRational::zero()),
            hi: Bnd::PosInf,
        }),
        Rel::Ge => Some(Ival {
            lo: Bnd::closed(BigRational::zero()),
            hi: Bnd::PosInf,
        }),
        Rel::Lt => Some(Ival {
            lo: Bnd::NegInf,
            hi: Bnd::open(BigRational::zero()),
        }),
        Rel::Le => Some(Ival {
            lo: Bnd::NegInf,
            hi: Bnd::closed(BigRational::zero()),
        }),
        Rel::Ne => None,
    }
}

/// Whether the (over-approximated) forward interval WHOLLY violates the
/// relation — every value in it falsifies `value REL 0`.
fn rel_violated(rel: Rel, iv: &Ival) -> bool {
    match rel {
        Rel::Eq => !iv.contains_zero(),
        // `!= 0` is violated only by the exact closed point {0}.
        Rel::Ne => {
            iv.lo == Bnd::closed(BigRational::zero()) && iv.hi == Bnd::closed(BigRational::zero())
        }
        // `> 0` violated when sup <= 0 (no value can be positive).
        Rel::Gt => matches!(&iv.hi, Bnd::Fin(v, _) if !v.is_positive()),
        // `>= 0` violated when the whole interval is < 0.
        Rel::Ge => iv.strictly_negative(),
        Rel::Lt => matches!(&iv.lo, Bnd::Fin(v, _) if !v.is_negative()),
        Rel::Le => iv.strictly_positive(),
    }
}

/// Forward interval of one monomial `coeff * prod x^k` over the current box.
fn eval_monomial(
    mono: &Monomial,
    coeff: &BigRational,
    dom: &BTreeMap<TermId, Ival>,
    meter: &mut WorkMeter<'_>,
) -> Result<Ival, String> {
    let mut acc = Ival::point(BigRational::one());
    for &(v, k) in mono {
        let d = dom
            .get(&v)
            .ok_or_else(|| "internal: variable missing from box".to_string())?;
        acc = acc.mul(&d.pow(k, meter)?, meter)?;
    }
    acc.scale(coeff, meter)
}

/// One HC4 revise of a single constraint against the box. `Ok(true)` means
/// the box is proven empty of solutions (REFUTED).
fn revise_constraint(
    c: &Constraint,
    dom: &mut BTreeMap<TermId, Ival>,
    meter: &mut WorkMeter<'_>,
) -> Result<bool, String> {
    // Monomials in BTreeMap order — deterministic.
    let monos: Vec<(&Monomial, &BigRational)> = c.poly.terms.iter().collect();
    let mut ivs: Vec<Ival> = Vec::with_capacity(monos.len());
    for (m, coeff) in &monos {
        ivs.push(eval_monomial(m, coeff, dom, meter)?);
    }
    let mut forward = Ival::point(BigRational::zero());
    for iv in &ivs {
        forward = forward.add(iv, meter)?;
    }
    if rel_violated(c.rel, &forward) {
        return Ok(true);
    }
    let Some(target) = rel_target(c.rel) else {
        return Ok(false);
    };

    // Prefix/suffix interval sums (interval subtraction does not cancel, so
    // "total minus this one" would be wrong; prefix+suffix is exact).
    let n = ivs.len();
    let mut prefix: Vec<Ival> = Vec::with_capacity(n + 1);
    prefix.push(Ival::point(BigRational::zero()));
    for iv in &ivs {
        let last = prefix.last().cloned().unwrap_or_else(Ival::full);
        prefix.push(last.add(iv, meter)?);
    }
    let mut suffix: Vec<Ival> = vec![Ival::point(BigRational::zero()); n + 1];
    for i in (0..n).rev() {
        suffix[i] = suffix[i + 1].add(&ivs[i], meter)?;
    }

    for (i, (mono, coeff)) in monos.iter().enumerate() {
        if mono.is_empty() {
            continue;
        }
        let others = prefix[i].add(&suffix[i + 1], meter)?;
        // The monomial must lie in (target - others) AND in its own forward
        // interval; an empty intersection proves the box solution-free.
        let tm = ivs[i].intersect(&target.add(&others.neg(), meter)?);
        if tm.is_empty() {
            return Ok(true);
        }
        // coeff is nonzero (MPoly never stores zero coefficients).
        let tpi = tm.scale(&(BigRational::one() / *coeff), meter)?;
        for &(x, k) in mono.iter() {
            // Cofactor product of the OTHER variable powers in this monomial.
            let mut r = Ival::point(BigRational::one());
            for &(y, j) in mono.iter() {
                if y == x {
                    continue;
                }
                let dy = dom
                    .get(&y)
                    .ok_or_else(|| "internal: variable missing from box".to_string())?;
                r = r.mul(&dy.pow(j, meter)?, meter)?;
            }
            let Some(rinv) = r.inv(meter)? else {
                // 0 is a member of the cofactor: division undefined — skip
                // this variable (skipping any narrowing step is sound).
                continue;
            };
            let txk = tpi.mul(&rinv, meter)?;
            let dx = dom
                .get(&x)
                .ok_or_else(|| "internal: variable missing from box".to_string())?
                .clone();
            let newpow = dx.pow(k, meter)?.intersect(&txk);
            if newpow.is_empty() {
                return Ok(true);
            }
            if let Some(narrowed) = narrow_var_from_pow(&newpow, k, meter)? {
                if narrowed.is_empty() {
                    return Ok(true);
                }
                let nd = dx.intersect(&narrowed);
                if nd.is_empty() {
                    return Ok(true);
                }
                dom.insert(x, nd);
            }
        }
    }
    Ok(false)
}

/// Derive a domain narrowing for `x` from a narrowed interval for `x^k`.
/// `None` = no narrowing derivable (sound: keep the current domain).
fn narrow_var_from_pow(
    powiv: &Ival,
    k: u32,
    meter: &mut WorkMeter<'_>,
) -> Result<Option<Ival>, String> {
    if k == 1 {
        return Ok(Some(powiv.clone()));
    }
    if k % 2 == 1 {
        // Odd power: strictly monotone, invert both ends with OUTWARD
        // rational root bounds. An inexact outward bound is strictly outside
        // the true root, so it may honestly stay OPEN; an exact bound
        // preserves the endpoint's openness.
        let lo = odd_root_lower(&powiv.lo, k, meter)?;
        let hi = odd_root_upper(&powiv.hi, k, meter)?;
        return Ok(Some(Ival { lo, hi }));
    }
    // Even power: an upper bound u on x^k bounds |x| by u^(1/k). A positive
    // LOWER bound would split the domain into two rays — SKIPPED (keeping
    // the hull is sound).
    match &powiv.hi {
        Bnd::PosInf => Ok(None),
        Bnd::NegInf => Ok(Some(Ival::empty())),
        Bnd::Fin(u, uo) => {
            match u.cmp(&BigRational::zero()) {
                std::cmp::Ordering::Less => {
                    // x^k (even) is nonnegative; an upper bound < 0 is
                    // outright infeasible.
                    Ok(Some(Ival::empty()))
                }
                std::cmp::Ordering::Equal => {
                    if *uo {
                        // x^k < 0: infeasible for even k.
                        Ok(Some(Ival::empty()))
                    } else {
                        // x^k <= 0 and x^k >= 0 force x = 0 exactly.
                        Ok(Some(Ival::point(BigRational::zero())))
                    }
                }
                std::cmp::Ordering::Greater => {
                    let (_, up, exact) = rat_nth_root_bounds(u, k, meter)?;
                    // Exact root: |x| <= root, openness follows u's. Inexact:
                    // up is STRICTLY outside the true root, so the open
                    // interval (-up, up) still contains every solution.
                    let open = if exact { *uo } else { true };
                    Ok(Some(Ival {
                        lo: Bnd::Fin(-&up, open),
                        hi: Bnd::Fin(up, open),
                    }))
                }
            }
        }
    }
}

/// Outward rational LOWER bound for `x` given `x^k >= bound` (odd `k`).
fn odd_root_lower(b: &Bnd, k: u32, meter: &mut WorkMeter<'_>) -> Result<Bnd, String> {
    Ok(match b {
        Bnd::NegInf => Bnd::NegInf,
        Bnd::PosInf => Bnd::PosInf,
        Bnd::Fin(v, o) => {
            if v >= &BigRational::zero() {
                let (lo, _, exact) = rat_nth_root_bounds(v, k, meter)?;
                // Inexact lo < root: x >= root > lo, so open is honest.
                Bnd::Fin(lo, if exact { *o } else { true })
            } else {
                let (_, up, exact) = rat_nth_root_bounds(&-v, k, meter)?;
                Bnd::Fin(-up, if exact { *o } else { true })
            }
        }
    })
}

/// Outward rational UPPER bound for `x` given `x^k <= bound` (odd `k`).
fn odd_root_upper(b: &Bnd, k: u32, meter: &mut WorkMeter<'_>) -> Result<Bnd, String> {
    Ok(match b {
        Bnd::PosInf => Bnd::PosInf,
        Bnd::NegInf => Bnd::NegInf,
        Bnd::Fin(v, o) => {
            if v >= &BigRational::zero() {
                let (_, up, exact) = rat_nth_root_bounds(v, k, meter)?;
                Bnd::Fin(up, if exact { *o } else { true })
            } else {
                let (lo, _, exact) = rat_nth_root_bounds(&-v, k, meter)?;
                Bnd::Fin(-lo, if exact { *o } else { true })
            }
        }
    })
}

#[cfg(test)]
#[path = "nra_interval_tests.rs"]
mod nra_interval_tests;
