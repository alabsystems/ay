// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict semantic validation for `TheoryLemmaKind::NraUnivariateUnsat`.
//!
//! # The obligation
//!
//! An `NraUnivariateUnsat` lemma claims: "the NEGATION of this clause is a
//! conjunction of polynomial sign constraints in exactly ONE variable, and
//! the conjunction is infeasible over the reals". The checker re-decides
//! the whole question with ITS OWN exact `BigRational` Sturm-based cell
//! decomposition; the kind carries no payload, so there is nothing to forge.
//!
//! # The decision (complete univariate case analysis)
//!
//! 1. Square-free parts `sf(p_i) = p_i / gcd(p_i, p_i')` by EXACT rational
//!    Euclidean remainders — the only normalization is division by POSITIVE
//!    content, which preserves every sign (the classic pseudo-remainder
//!    sign-flip unsoundness is structurally impossible: no pseudo-remainders
//!    are used).
//! 2. Root-superset polynomial `S = sf(prod_i sf(p_i))`, so
//!    `roots(S) = union_i roots(p_i)`, each simple.
//! 3. Sturm chain of `S`; Cauchy bound `M` (every real root lies STRICTLY
//!    inside `(-M, M)`, so `±M` are safe counting points).
//! 4. Root isolation by bisection. A bisection midpoint that hits a root is
//!    an EXACT rational root: it is bracketed by a shrinking `±δ` window and
//!    recorded as a point root; counting endpoints are always non-roots.
//! 5. Cells `(-inf, r_1), {r_1}, (r_1, r_2), …, {r_N}, (r_N, +inf)`. On open
//!    cells every `p_i` is sign-constant (its roots are all among the `r_j`,
//!    which open cells exclude), so ONE rational sample decides the sign —
//!    a theorem here, not a hope. On a root cell `{r_j}` the zero test is
//!    ALGEBRAIC: `g = gcd(S, sf(p_i))` has a root in the isolating interval
//!    (decided by `g`'s own Sturm count — well-defined because `g | S`, so
//!    `g` is nonzero at the interval's non-root-of-`S` endpoints) iff
//!    `p_i(r_j) = 0`; otherwise `p_i` is sign-constant on the WHOLE
//!    isolating interval and a rational sample decides it.
//! 6. The cells partition R and every `p_i` is sign-invariant per cell, so
//!    the conjunction is satisfiable iff SOME cell's sign vector satisfies
//!    every relation. "No cell satisfies" literally IS infeasibility over R.
//!
//! # Why rational-only sampling would be UNSOUND
//!
//! A checker that samples only rational points concludes "no satisfying
//! point" for systems whose only solutions are irrational algebraic numbers:
//! `{x^2 = 2, x > 0}` is satisfiable exactly at `x = sqrt(2)`, yet every
//! rational `x` gives `x^2 != 2`. Sign-at-the-root must be decided
//! algebraically (gcd + Sturm count) and root cells must exist as
//! first-class cells — step 5 does exactly that, and the forgery tests pin
//! the trap shut.
//!
//! Any unsupported shape, foreign variable count, degree, or budget trip:
//! `Err` — fail-closed to the pre-existing `Generic` rejection.

use ay_core::{ProofId, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use super::nra_poly::{
    bit_scaled, extract_constraints, max_coeff_bits, MPoly, Rel, WorkMeter, MAX_BISECTION_STEPS,
    MAX_POLY_DEGREE, MAX_STURM_CHAIN_BITS,
};
use super::ProofCheckError;

/// Whether the negation of the clause is a conjunction of polynomial sign
/// constraints in exactly ONE variable that the checker's OWN exact
/// Sturm-based cell decomposition proves infeasible over the reals.
///
/// This is the EXACT precondition of `validate_nra_univariate_unsat`, so
/// the proof classifier in `ay-dpll` can only assign the kind to lemmas
/// strict mode will then accept — no classifier/checker drift. All decision
/// logic lives ONLY in this module and the shared `nra_poly` kernel.
#[must_use]
pub fn recognize_nra_univariate_unsat(terms: &TermStore, clause: &[TermId]) -> bool {
    decide_nra_univariate_unsat(terms, clause).is_ok()
}

/// Validate a `TheoryLemmaKind::NraUnivariateUnsat` lemma in strict mode.
pub(crate) fn validate_nra_univariate_unsat(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    decide_nra_univariate_unsat(terms, clause).map_err(|reason| {
        ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: format!("nra_univariate_unsat: {reason}"),
        }
    })
}

/// The single deciding routine both the recognizer and validator call
/// (recognize == validate-success by construction). Deterministic:
/// `BTreeMap`/`Vec`-only iteration, fresh work meter per call.
fn decide_nra_univariate_unsat(terms: &TermStore, clause: &[TermId]) -> Result<(), String> {
    let mut meter = WorkMeter::new();
    let ext = extract_constraints(terms, clause, &mut meter)?;
    if !ext.has_nonlinear {
        return Err(
            "no monomial of degree >= 2; linear conflicts stay in the LRA/LIA lanes".to_string(),
        );
    }
    if ext.const_refuted {
        // A constant conjunct of the negated clause is FALSE: the conjunction
        // is infeasible outright and the clause is valid. NOTE this accepts
        // BEFORE the one-variable shape check — a multivariate clause with a
        // false constant conjunct certifies under this kind without a Sturm
        // run. Semantically sound (the refutation is the false constant, not
        // a univariate argument); documented on the enum variant.
        return Ok(());
    }
    if ext.constraints.is_empty() {
        return Err("no surviving constraints; an empty conjunction is unrefutable".to_string());
    }
    if ext.vars.len() != 1 {
        return Err(format!(
            "univariate kind requires exactly one variable, found {}",
            ext.vars.len()
        ));
    }
    let var = *ext
        .vars
        .iter()
        .next()
        .ok_or_else(|| "internal: missing variable".to_string())?;

    // Convert to dense univariate polynomials.
    let mut system: Vec<(UPoly, Rel)> = Vec::with_capacity(ext.constraints.len());
    for c in &ext.constraints {
        system.push((to_univariate(&c.poly, var)?, c.rel));
    }

    // Root-superset polynomial S = sf(prod sf(p_i)).
    let mut prod = vec![BigRational::one()];
    let mut sf_cache: Vec<UPoly> = Vec::with_capacity(system.len());
    for (p, _) in &system {
        let sf = square_free_part(p, &mut meter)?;
        prod = poly_mul(&prod, &sf, &mut meter)?;
        if poly_deg(&prod).unwrap_or(0) > MAX_POLY_DEGREE as usize {
            return Err(format!(
                "root-superset polynomial degree exceeds cap {MAX_POLY_DEGREE}"
            ));
        }
        sf_cache.push(sf);
    }
    let s = square_free_part(&prod, &mut meter)?;
    let s = content_normalize(&s, &mut meter)?;
    let s_deg = poly_deg(&s).ok_or_else(|| "internal: zero root-superset".to_string())?;

    // Per-constraint algebraic zero-test machinery: g_i = gcd(S, sf(p_i)),
    // and g_i's own Sturm chain when non-constant.
    let mut zero_tests: Vec<Option<Vec<UPoly>>> = Vec::with_capacity(system.len());
    if s_deg >= 1 {
        for sf in &sf_cache {
            let g = poly_gcd(&s, sf, &mut meter)?;
            if poly_deg(&g).unwrap_or(0) >= 1 {
                zero_tests.push(Some(sturm_chain(&g, &mut meter)?));
            } else {
                zero_tests.push(None);
            }
        }
    } else {
        zero_tests.resize_with(system.len(), || None);
    }

    // Isolate the roots of S.
    let locs = if s_deg == 0 {
        Vec::new()
    } else {
        let chain = sturm_chain(&s, &mut meter)?;
        let m = cauchy_bound(&s)?;
        isolate_roots(&chain, &s, &m, &mut meter)?
    };

    // Cell scan: (-inf, r_1), {r_1}, (r_1, r_2), ..., {r_N}, (r_N, +inf).
    // The conjunction is satisfiable iff some cell's sign vector satisfies
    // every relation; accept ONLY when no cell does.
    let sample_cells = open_cell_samples(&s, &locs, &mut meter)?;
    let mut cells: Vec<Cell<'_>> = Vec::with_capacity(2 * locs.len() + 1);
    for (i, sample) in sample_cells.iter().enumerate() {
        cells.push(Cell::Open(sample.clone()));
        if i < locs.len() {
            cells.push(Cell::Root(&locs[i]));
        }
    }
    for cell in &cells {
        if cell_satisfies_all(cell, &system, &zero_tests, &mut meter)? {
            return Err(
                "the negated clause is SATISFIABLE over the reals (a sign-invariant cell \
                 satisfies every constraint); the lemma is not valid"
                    .to_string(),
            );
        }
    }
    Ok(())
}

// ============================================================================
// Cells
// ============================================================================

/// One isolated real root of the root-superset polynomial `S`.
#[derive(Clone, Debug)]
enum RootLoc {
    /// An exact rational root `m`, bracketed by non-roots `lo < m < hi`.
    Exact {
        m: BigRational,
        lo: BigRational,
        hi: BigRational,
    },
    /// An isolated (generally irrational) root in `(lo, hi)`, both endpoints
    /// non-roots of `S`, exactly one root of `S` inside.
    Alg { lo: BigRational, hi: BigRational },
}

impl RootLoc {
    fn lo(&self) -> &BigRational {
        match self {
            Self::Exact { lo, .. } | Self::Alg { lo, .. } => lo,
        }
    }
    fn hi(&self) -> &BigRational {
        match self {
            Self::Exact { hi, .. } | Self::Alg { hi, .. } => hi,
        }
    }
}

enum Cell<'a> {
    /// An open cell between consecutive roots (or beyond the extremes),
    /// carrying its rational sample point.
    Open(BigRational),
    /// A root cell `{r_j}`.
    Root(&'a RootLoc),
}

/// Sample points for the open cells, in order: below the first root, between
/// consecutive roots, above the last root. With no roots at all, the single
/// cell R is sampled at 0.
fn open_cell_samples(
    s: &UPoly,
    locs: &[RootLoc],
    meter: &mut WorkMeter<'_>,
) -> Result<Vec<BigRational>, String> {
    if locs.is_empty() {
        return Ok(vec![BigRational::zero()]);
    }
    let m = cauchy_bound(s)?;
    let mut out = Vec::with_capacity(locs.len() + 1);
    out.push(-m.clone());
    for w in locs.windows(2) {
        let hi_prev = w[0].hi();
        let lo_next = w[1].lo();
        // Both are non-roots of S in the open gap between the two roots; any
        // rational in [hi_prev, lo_next] lies strictly between the roots.
        let sample = if hi_prev <= lo_next {
            (hi_prev + lo_next) / BigRational::from_integer(BigInt::from(2))
        } else {
            return Err("internal: isolating intervals out of order".to_string());
        };
        out.push(sample);
    }
    out.push(m);
    meter.charge_ops(locs.len() as u64)?;
    Ok(out)
}

/// Whether one cell's sign vector satisfies EVERY constraint.
fn cell_satisfies_all(
    cell: &Cell<'_>,
    system: &[(UPoly, Rel)],
    zero_tests: &[Option<Vec<UPoly>>],
    meter: &mut WorkMeter<'_>,
) -> Result<bool, String> {
    for (i, (p, rel)) in system.iter().enumerate() {
        let sign = match cell {
            Cell::Open(sample) => poly_eval(p, sample, meter)?.cmp(&BigRational::zero()),
            Cell::Root(loc) => root_cell_sign(p, loc, zero_tests.get(i), meter)?,
        };
        if !rel.satisfied_by_sign(sign) {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Exact sign of `p` at the root cell `{r_j}`.
fn root_cell_sign(
    p: &UPoly,
    loc: &RootLoc,
    zero_test: Option<&Option<Vec<UPoly>>>,
    meter: &mut WorkMeter<'_>,
) -> Result<std::cmp::Ordering, String> {
    match loc {
        RootLoc::Exact { m, .. } => Ok(poly_eval(p, m, meter)?.cmp(&BigRational::zero())),
        RootLoc::Alg { lo, hi } => {
            let is_zero_at_root = match zero_test {
                Some(Some(chain_g)) => {
                    // Roots of g in (lo, hi): 0 or 1 (g | S and the interval
                    // isolates one root of S). 1 means p(r_j) = 0.
                    let vl = sign_variations(chain_g, lo, meter)?;
                    let vh = sign_variations(chain_g, hi, meter)?;
                    if vl < vh {
                        return Err("sturm variation anomaly (gcd chain)".to_string());
                    }
                    vl - vh >= 1
                }
                Some(None) => false, // gcd constant: p has no root among roots(S)
                None => return Err("internal: missing zero-test entry".to_string()),
            };
            if is_zero_at_root {
                return Ok(std::cmp::Ordering::Equal);
            }
            // p(r_j) != 0, and p is sign-constant on the WHOLE isolating
            // interval (its roots all lie among roots(S), and the interval
            // contains no root of S other than r_j, which is not a root of
            // p). Sample the rational midpoint.
            let mid = (lo + hi) / BigRational::from_integer(BigInt::from(2));
            let v = poly_eval(p, &mid, meter)?;
            if v.is_zero() {
                // Mathematically impossible in this branch; refuse rather
                // than guess (fail closed).
                return Err("internal: unexpected zero at sign sample".to_string());
            }
            Ok(v.cmp(&BigRational::zero()))
        }
    }
}

// ============================================================================
// Root isolation
// ============================================================================

/// Isolate every real root of `S` inside `(-M, M)` via Sturm bisection.
/// Returned locations are sorted, pairwise disjoint (adjacent brackets may
/// share a non-root endpoint), each containing exactly one root of `S`.
fn isolate_roots(
    chain: &[UPoly],
    s: &UPoly,
    m: &BigRational,
    meter: &mut WorkMeter<'_>,
) -> Result<Vec<RootLoc>, String> {
    let two = BigRational::from_integer(BigInt::from(2));
    let neg_m = -m.clone();
    let va = sign_variations(chain, &neg_m, meter)?;
    let vb = sign_variations(chain, m, meter)?;
    if va < vb {
        return Err("sturm variation anomaly".to_string());
    }

    enum Work {
        Seg {
            a: BigRational,
            b: BigRational,
            va: usize,
            vb: usize,
        },
        Emit(RootLoc),
    }
    let mut out: Vec<RootLoc> = Vec::new();
    let mut steps = 0usize;
    let mut stack = vec![Work::Seg {
        a: neg_m,
        b: m.clone(),
        va,
        vb,
    }];
    while let Some(w) = stack.pop() {
        match w {
            Work::Emit(loc) => out.push(loc),
            Work::Seg { a, b, va, vb } => {
                if va < vb {
                    return Err("sturm variation anomaly".to_string());
                }
                let count = va - vb;
                if count == 0 {
                    continue;
                }
                if count == 1 {
                    out.push(RootLoc::Alg { lo: a, hi: b });
                    continue;
                }
                steps += 1;
                if steps > MAX_BISECTION_STEPS {
                    return Err("bisection step cap reached".to_string());
                }
                let mid = (&a + &b) / &two;
                if !poly_eval(s, &mid, meter)?.is_zero() {
                    let vm = sign_variations(chain, &mid, meter)?;
                    // LIFO: push the RIGHT segment first so the LEFT pops
                    // first and the output stays sorted.
                    stack.push(Work::Seg {
                        a: mid.clone(),
                        b,
                        va: vm,
                        vb,
                    });
                    stack.push(Work::Seg {
                        a,
                        b: mid,
                        va,
                        vb: vm,
                    });
                } else {
                    // mid is an EXACT rational root. Shrink a ±δ bracket
                    // until it contains only this root and its endpoints are
                    // non-roots; δ halves each round, so this terminates.
                    let mut delta = {
                        let left = &mid - &a;
                        let right = &b - &mid;
                        (if left < right { left } else { right }) / &two
                    };
                    let (l, r, vl, vr) = loop {
                        steps += 1;
                        if steps > MAX_BISECTION_STEPS {
                            return Err("bisection step cap reached".to_string());
                        }
                        let l = &mid - &delta;
                        let r = &mid + &delta;
                        if !poly_eval(s, &l, meter)?.is_zero()
                            && !poly_eval(s, &r, meter)?.is_zero()
                        {
                            let vl = sign_variations(chain, &l, meter)?;
                            let vr = sign_variations(chain, &r, meter)?;
                            if vl < vr {
                                return Err("sturm variation anomaly".to_string());
                            }
                            if vl - vr == 1 {
                                break (l, r, vl, vr);
                            }
                        }
                        delta = &delta / &two;
                    };
                    stack.push(Work::Seg {
                        a: r.clone(),
                        b,
                        va: vr,
                        vb,
                    });
                    stack.push(Work::Emit(RootLoc::Exact {
                        m: mid,
                        lo: l.clone(),
                        hi: r,
                    }));
                    stack.push(Work::Seg {
                        a,
                        b: l,
                        va,
                        vb: vl,
                    });
                }
            }
        }
    }
    Ok(out)
}

// ============================================================================
// Dense univariate polynomials over BigRational
// ============================================================================

/// Dense coefficients, low degree first, no trailing zeros (empty = zero).
type UPoly = Vec<BigRational>;

fn to_univariate(poly: &MPoly, var: TermId) -> Result<UPoly, String> {
    let deg = poly.max_total_degree() as usize;
    let mut coeffs = vec![BigRational::zero(); deg + 1];
    for (m, c) in &poly.terms {
        match m.as_slice() {
            [] => coeffs[0] += c,
            [(v, k)] if *v == var => {
                let k = *k as usize;
                if k >= coeffs.len() {
                    return Err("internal: univariate degree mismatch".to_string());
                }
                coeffs[k] += c;
            }
            _ => return Err("monomial mentions a foreign variable".to_string()),
        }
    }
    poly_trim(&mut coeffs);
    Ok(coeffs)
}

fn poly_trim(p: &mut UPoly) {
    while p.last().is_some_and(Zero::is_zero) {
        p.pop();
    }
}

fn poly_is_zero(p: &UPoly) -> bool {
    p.is_empty()
}

/// Degree, `None` for the zero polynomial.
fn poly_deg(p: &UPoly) -> Option<usize> {
    p.len().checked_sub(1)
}

fn poly_eval(p: &UPoly, x: &BigRational, meter: &mut WorkMeter<'_>) -> Result<BigRational, String> {
    // Horner on n-bit rational points: the accumulator gains ~bits(x) per
    // step, so total work is quadratic in the length — sum over steps of
    // k*bits(x) is n^2*bits(x)/2 — plus the coefficients' own width.
    let n = p.len() as u64;
    let x_bits = super::nra_poly::rat_bits(x);
    meter.charge_ops(
        bit_scaled(n.saturating_mul(n) / 2 + 1, x_bits)
            + bit_scaled(n, max_coeff_bits(p.iter()))
            + 1,
    )?;
    let mut acc = BigRational::zero();
    for c in p.iter().rev() {
        acc = acc * x + c;
    }
    Ok(acc)
}

fn poly_neg(p: &UPoly) -> UPoly {
    p.iter().map(|c| -c).collect()
}

fn poly_mul(a: &UPoly, b: &UPoly, meter: &mut WorkMeter<'_>) -> Result<UPoly, String> {
    if poly_is_zero(a) || poly_is_zero(b) {
        return Ok(Vec::new());
    }
    let bits = max_coeff_bits(a.iter()).max(max_coeff_bits(b.iter()));
    meter.charge_ops(bit_scaled((a.len() * b.len()) as u64, bits))?;
    let mut out = vec![BigRational::zero(); a.len() + b.len() - 1];
    for (i, ca) in a.iter().enumerate() {
        for (j, cb) in b.iter().enumerate() {
            out[i + j] += ca * cb;
        }
    }
    poly_trim(&mut out);
    Ok(out)
}

fn poly_derivative(p: &UPoly, meter: &mut WorkMeter<'_>) -> Result<UPoly, String> {
    meter.charge_ops(p.len() as u64 + 1)?;
    if p.len() <= 1 {
        return Ok(Vec::new());
    }
    let mut out = Vec::with_capacity(p.len() - 1);
    for (i, c) in p.iter().enumerate().skip(1) {
        out.push(c * BigRational::from_integer(BigInt::from(i)));
    }
    poly_trim(&mut out);
    Ok(out)
}

/// EXACT Euclidean polynomial remainder over `BigRational` — no
/// pseudo-remainders, so no sign-flipping scaling exists to get wrong.
fn poly_rem(a: &UPoly, b: &UPoly, meter: &mut WorkMeter<'_>) -> Result<UPoly, String> {
    let db = poly_deg(b).ok_or_else(|| "polynomial division by zero".to_string())?;
    let lb = b
        .last()
        .ok_or_else(|| "polynomial division by zero".to_string())?;
    let mut r = a.clone();
    while let Some(dr) = poly_deg(&r) {
        if dr < db {
            break;
        }
        let factor = r
            .last()
            .map(|lr| lr / lb)
            .ok_or_else(|| "internal: empty remainder".to_string())?;
        // Euclidean remainder coefficients grow step over step; charge each
        // elimination row by the widths actually being multiplied so crafted
        // inputs trip the budget instead of grinding.
        let bits = super::nra_poly::rat_bits(&factor) + super::nra_poly::rat_bits(lb);
        meter.charge_ops(bit_scaled(db as u64 + 2, bits))?;
        let shift = dr - db;
        for i in 0..=db {
            let delta = &factor * &b[i];
            r[shift + i] -= delta;
        }
        poly_trim(&mut r);
    }
    Ok(r)
}

/// EXACT polynomial quotient when `d` divides `p`; `Err` on a nonzero
/// remainder (fail closed — never guess).
fn poly_div_exact(p: &UPoly, d: &UPoly, meter: &mut WorkMeter<'_>) -> Result<UPoly, String> {
    let dd = poly_deg(d).ok_or_else(|| "polynomial division by zero".to_string())?;
    let ld = d
        .last()
        .ok_or_else(|| "polynomial division by zero".to_string())?;
    let dp = match poly_deg(p) {
        None => return Ok(Vec::new()),
        Some(dp) if dp < dd => return Err("inexact polynomial division".to_string()),
        Some(dp) => dp,
    };
    let mut r = p.clone();
    let mut q = vec![BigRational::zero(); dp - dd + 1];
    while let Some(dr) = poly_deg(&r) {
        if dr < dd {
            break;
        }
        let factor = r
            .last()
            .map(|lr| lr / ld)
            .ok_or_else(|| "internal: empty remainder".to_string())?;
        let bits = super::nra_poly::rat_bits(&factor) + super::nra_poly::rat_bits(ld);
        meter.charge_ops(bit_scaled(dd as u64 + 2, bits))?;
        let shift = dr - dd;
        q[shift] = factor.clone();
        for i in 0..=dd {
            let delta = &factor * &d[i];
            r[shift + i] -= delta;
        }
        poly_trim(&mut r);
    }
    if !poly_is_zero(&r) {
        return Err("inexact polynomial division".to_string());
    }
    poly_trim(&mut q);
    Ok(q)
}

/// Scale by the POSITIVE rational that makes the coefficients a primitive
/// integer vector. Positive scaling is sign-faithful — the entire
/// normalization obligation for a Sturm chain.
fn content_normalize(p: &UPoly, meter: &mut WorkMeter<'_>) -> Result<UPoly, String> {
    if poly_is_zero(p) {
        return Ok(Vec::new());
    }
    meter.charge_ops(bit_scaled(p.len() as u64 * 2, max_coeff_bits(p.iter())))?;
    let mut denom_lcm = BigInt::one();
    for c in p {
        let d = c.denom();
        let g = bigint_gcd(&denom_lcm, d);
        if g.is_zero() {
            return Err("internal: zero gcd".to_string());
        }
        denom_lcm = &denom_lcm / &g * d;
    }
    let mut numer_gcd = BigInt::zero();
    for c in p {
        // c * denom_lcm is an integer: numer * (denom_lcm / denom).
        let scaled = c.numer() * (&denom_lcm / c.denom());
        numer_gcd = bigint_gcd(&numer_gcd, &scaled);
    }
    if numer_gcd.is_zero() {
        return Ok(Vec::new());
    }
    let scale = BigRational::new(denom_lcm, numer_gcd);
    // scale > 0: lcm > 0 and gcd > 0 by construction.
    Ok(p.iter().map(|c| c * &scale).collect())
}

fn bigint_gcd(a: &BigInt, b: &BigInt) -> BigInt {
    let mut a = a.abs();
    let mut b = b.abs();
    while !b.is_zero() {
        let r = &a % &b;
        a = b;
        b = r;
    }
    a
}

/// Polynomial gcd by exact Euclid with per-step content normalization.
/// Returns a content-normalized gcd; a constant gcd is returned as `[1]`.
fn poly_gcd(a: &UPoly, b: &UPoly, meter: &mut WorkMeter<'_>) -> Result<UPoly, String> {
    let mut x = content_normalize(a, meter)?;
    let mut y = content_normalize(b, meter)?;
    if poly_deg(&x) < poly_deg(&y) {
        std::mem::swap(&mut x, &mut y);
    }
    while !poly_is_zero(&y) {
        let r = poly_rem(&x, &y, meter)?;
        x = y;
        y = content_normalize(&r, meter)?;
    }
    if poly_deg(&x).unwrap_or(0) == 0 && !poly_is_zero(&x) {
        return Ok(vec![BigRational::one()]);
    }
    Ok(x)
}

/// Square-free part `p / gcd(p, p')` (root set preserved, all roots simple).
fn square_free_part(p: &UPoly, meter: &mut WorkMeter<'_>) -> Result<UPoly, String> {
    let d = poly_deg(p).ok_or_else(|| "square-free part of zero polynomial".to_string())?;
    if d == 0 {
        return content_normalize(p, meter);
    }
    let dp = poly_derivative(p, meter)?;
    let g = poly_gcd(p, &dp, meter)?;
    if poly_deg(&g).unwrap_or(0) == 0 {
        return content_normalize(p, meter);
    }
    let sf = poly_div_exact(p, &g, meter)?;
    content_normalize(&sf, meter)
}

/// Canonical Sturm chain of a SQUARE-FREE polynomial: `s, s', then
/// `-rem(prev, cur)` with positive-content normalization per step. Ends in a
/// nonzero constant (verified — a non-constant tail means the input was not
/// square-free, which is refused).
fn sturm_chain(s: &UPoly, meter: &mut WorkMeter<'_>) -> Result<Vec<UPoly>, String> {
    let d = poly_deg(s).ok_or_else(|| "sturm chain of zero polynomial".to_string())?;
    let s0 = content_normalize(s, meter)?;
    if d == 0 {
        return Ok(vec![s0]);
    }
    let s1 = content_normalize(&poly_derivative(&s0, meter)?, meter)?;
    let mut chain = vec![s0, s1];
    let mut bits: u64 = 0;
    loop {
        let n = chain.len();
        let (prev, cur) = (&chain[n - 2], &chain[n - 1]);
        if poly_is_zero(cur) {
            return Err("sturm chain degenerated (input not square-free)".to_string());
        }
        if poly_deg(cur) == Some(0) {
            break;
        }
        let r = poly_rem(prev, cur, meter)?;
        if poly_is_zero(&r) {
            return Err("sturm chain degenerated (input not square-free)".to_string());
        }
        let next = content_normalize(&poly_neg(&r), meter)?;
        bits += poly_bits(&next);
        if bits > MAX_STURM_CHAIN_BITS {
            return Err("sturm chain coefficient budget exceeded".to_string());
        }
        chain.push(next);
    }
    Ok(chain)
}

fn poly_bits(p: &UPoly) -> u64 {
    p.iter().map(|c| c.numer().bits() + c.denom().bits()).sum()
}

/// Number of sign variations of the chain at `x`, zeros skipped. Only valid
/// at non-roots of the chain head — every caller guarantees that.
fn sign_variations(
    chain: &[UPoly],
    x: &BigRational,
    meter: &mut WorkMeter<'_>,
) -> Result<usize, String> {
    let mut last: Option<bool> = None; // sign as "is_positive"
    let mut count = 0usize;
    for p in chain {
        let v = poly_eval(p, x, meter)?;
        if v.is_zero() {
            continue;
        }
        let pos = v.is_positive();
        if let Some(prev) = last {
            if prev != pos {
                count += 1;
            }
        }
        last = Some(pos);
    }
    Ok(count)
}

/// Cauchy root bound `M = 1 + max_i |a_i| / |a_n|`: every real root of the
/// polynomial satisfies `|x| < M` STRICTLY, so `±M` are safe non-root
/// counting points.
fn cauchy_bound(p: &UPoly) -> Result<BigRational, String> {
    let lead = p
        .last()
        .filter(|c| !c.is_zero())
        .ok_or_else(|| "cauchy bound of zero polynomial".to_string())?;
    let mut max = BigRational::zero();
    for c in &p[..p.len() - 1] {
        let ratio = (c / lead).abs();
        if ratio > max {
            max = ratio;
        }
    }
    Ok(max + BigRational::one())
}

#[cfg(test)]
#[path = "nra_univariate_tests.rs"]
mod nra_univariate_tests;
