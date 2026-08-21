// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Differential checks for `crates/ay-theories/nra/src/subresultant.rs` — the
//! fraction-free subresultant / psc-chain substrate on the CAD projection path.
//!
//! # Why this module exists separately
//!
//! The checks in [`crate::checks`] certify primitives AY has shipped for years:
//! root isolation, gcd, Sturm counting, and a `resultant` that resolves to
//! `algebraic.rs::sylvester_det_fixed`. None of them execute a single line of
//! `subresultant.rs`, whose whole surface is `pub(crate)` inside a private
//! `mod`. A clean run of the univariate campaign therefore said exactly nothing
//! about the newest and least-guarded code in the crate.
//!
//! # The two comparisons
//!
//! **Univariate.** `Z3_polynomial_subresultants(f, g, x)` returns the NON-ZERO
//! principal subresultant coefficients in ascending index order, with the empty
//! chain encoded as the single element `0`. AY's `psc_chain` returns `psc_j`
//! for `j` in `0..deg(min)` *including* zeros. So the mapping is
//!
//! ```text
//!     [ c for c in AY.psc_chain(f, g) if c != 0 ]  ==  z3.subresultants(f, g)
//! ```
//!
//! which compares the ENTIRE chain, not just `psc_0`. That matters: the
//! existing `resultant` check only ever looked at `psc_0`, so a defect in a
//! higher chain entry — precisely what a defective (degree-gap) PRS step
//! computes — was invisible to it.
//!
//! **Bivariate.** This is the shape CAD projection actually operates on and the
//! one the univariate oracle could not reach at all. z3's C API will happily
//! take bivariate arguments, but then it returns ASTs in `y` that would have to
//! be normalized before comparison — and an oracle that needs its own
//! polynomial normalizer to interpret the reference is an oracle that can
//! manufacture divergences. Instead this uses SPECIALIZATION:
//!
//! ```text
//!     psc_j(F, G)(x, y)  |_(y = c)   ==   psc_j( F(x, c), G(x, c) )
//! ```
//!
//! Subresultants are determinants in the coefficients, so they commute with any
//! ring homomorphism that preserves the degree in `x`. The check enforces that
//! side condition explicitly — `lc_x(F)(c) != 0` and `lc_x(G)(c) != 0` — and
//! skips otherwise rather than comparing something the theorem does not cover.
//! The z3 side then stays entirely inside the univariate numeral path that is
//! already known-good, while the AY side runs the full multivariate machinery:
//! `MPolyZ` multiplication, `pseudo_rem` over a non-field ring, and above all
//! `MPolyZ::exact_div`, the operation the entire fraction-free design rests on
//! and the one with no univariate fallback.

use ay_nra::oracle_api::{OBiPoly, OPoly, OYPoly, OZPoly};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::checks::{Divergence, Outcome, Sabotage};
use crate::polygen::{GenPoly, Rng};
use crate::z3::Z3;

/// Maximum degree in `x` for a generated bivariate polynomial.
///
/// Held low deliberately. The bivariate chain runs Bareiss elimination over
/// `MPolyZ`, so intermediate terms grow in BOTH degree and coefficient size;
/// at `4` the measured median case is sub-millisecond and the worst case stays
/// under a second, while degree `6` produced individual cases running for
/// minutes — which measures sparse-polynomial throughput, not agreement.
const MAX_BI_DEG_X: usize = 4;

/// Maximum degree in `y` of any single `x`-coefficient.
const MAX_BI_DEG_Y: usize = 3;

/// Convert a generated rational polynomial to an integer one by clearing
/// denominators. Subresultants are NOT scaling-invariant, so both sides must
/// see the same integer polynomial — this returns the coefficients actually
/// handed to z3 as well.
fn integral_coeffs(g: &GenPoly) -> Option<(OZPoly, Vec<BigRational>)> {
    if g.coeffs.is_empty() {
        return None;
    }
    let mut lcm = BigInt::one();
    for c in &g.coeffs {
        lcm = num_integer::lcm(lcm, c.denom().clone());
    }
    if lcm.is_negative() {
        lcm = -lcm;
    }
    let ints: Vec<BigInt> = g
        .coeffs
        .iter()
        .map(|c| (c.numer() * &lcm) / c.denom())
        .collect();
    let rats: Vec<BigRational> = ints.iter().map(|i| BigRational::from(i.clone())).collect();
    Some((OZPoly::from_ints(ints), rats))
}

fn render_ints(v: &[BigInt]) -> String {
    if v.is_empty() {
        return "0".to_string();
    }
    v.iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(", ")
}

/// Read z3's psc chain as integers. `None` if any entry is not a numeral (which
/// happens only if the inputs were not actually univariate).
fn z3_chain_ints(z3: &Z3, f: &[BigRational], g: &[BigRational]) -> Option<Vec<BigInt>> {
    let asts = z3.subresultants(f, g)?;
    let mut out = Vec::with_capacity(asts.len());
    for a in asts {
        let v = z3.numeral_value(a)?;
        if !v.denom().is_one() {
            return None;
        }
        out.push(v.numer().clone());
    }
    Some(out)
}

/// z3's chain, normalized to "the list of non-zero pscs, ascending".
///
/// z3 encodes the empty chain as the single element `0`; that is the only place
/// a zero can legitimately appear, so it maps to the empty list.
fn z3_nonzero_chain(raw: &[BigInt]) -> Vec<BigInt> {
    if raw.len() == 1 && raw[0].is_zero() {
        return Vec::new();
    }
    raw.iter().filter(|c| !c.is_zero()).cloned().collect()
}

/// `Res(f, g)` in z3's convention (arguments ordered higher-degree first), read
/// out of the psc chain.
///
/// # Why this is not just `raw[0]`
///
/// z3 omits EVERY vanishing psc, not merely leading ones, so the position of an
/// entry in the returned list does not identify its index and the list's LENGTH
/// carries no information about whether `psc_0` survived. Inferring
/// `Res = 0` from a short chain is wrong, and it is wrong in the direction that
/// manufactures divergences against correct code — it did so here twice, on
/// `x^6 - 519` (chain `[Res]`, because `psc_1..psc_4` all vanish) and on
/// equal-degree bivariate pairs.
///
/// `psc_0 = Res(f, g)` is zero exactly when `f` and `g` share a non-constant
/// factor. That is decided with AY's `gcd`, which is legitimate as a
/// discriminator precisely because the `gcd` check certifies it differentially
/// against z3 over the same corpus — it is not the primitive under test here.
pub(crate) fn z3_resultant(z3: &Z3, f: &[BigRational], g: &[BigRational]) -> Option<BigInt> {
    let raw = z3_chain_ints(z3, f, g)?;
    if raw.is_empty() {
        return None;
    }
    let coprime = OPoly::from_coeffs(f.to_vec())
        .gcd(&OPoly::from_coeffs(g.to_vec()))
        .degree()
        == Some(0);
    if coprime {
        // psc_0 != 0, so it is present and first.
        Some(raw[0].clone())
    } else {
        Some(BigInt::zero())
    }
}

/// **Univariate psc chain**: AY's `subresultant::psc_chain` against the full
/// `Z3_polynomial_subresultants` chain.
pub(crate) fn check_psc_chain(z3: &Z3, p: &GenPoly, q: &GenPoly, sab: Sabotage) -> Outcome {
    let (Some((ap, pr)), Some((aq, qr))) = (integral_coeffs(p), integral_coeffs(q)) else {
        return Outcome::Skipped("zero polynomial");
    };
    let (Some(dp), Some(dq)) = (ap.degree(), aq.degree()) else {
        return Outcome::Skipped("zero polynomial");
    };
    if dp < 1 || dq < 1 {
        return Outcome::Skipped("degree < 1");
    }
    if dp + dq > 12 {
        return Outcome::Skipped("degree sum too large");
    }
    let Some(mut chain) = ap.psc_chain(&aq) else {
        return Outcome::Declined("psc_chain");
    };
    // Sabotage: flip the sign of the last non-zero chain entry. Chosen so it
    // corrupts a HIGHER psc when one exists, which is exactly the region the
    // pre-existing psc_0-only resultant check could not see.
    if sab.on() {
        if let Some(last) = chain.iter_mut().rev().find(|c| !c.is_zero()) {
            *last = -last.clone();
        } else {
            chain.push(BigInt::one());
        }
    }
    let ay: Vec<BigInt> = chain.iter().filter(|c| !c.is_zero()).cloned().collect();

    let Some(raw) = z3_chain_ints(z3, &pr, &qr) else {
        return Outcome::Skipped("z3 declined");
    };
    if raw.is_empty() {
        return Outcome::Skipped("empty subresultant chain");
    }
    let want = z3_nonzero_chain(&raw);

    if ay != want {
        return Divergence::new(
            "psc-chain",
            "z3",
            format!(
                "AY non-zero psc chain [{}] but z3 [{}] (AY full chain [{}], deg {dp} vs {dq})",
                render_ints(&ay),
                render_ints(&want),
                render_ints(&chain),
            ),
            inputs_z(&ap, &aq),
        );
    }

    // Argument-order symmetry: Res(f, g) = (-1)^(deg f * deg g) * Res(g, f).
    //
    // This is an internal identity, not a z3 differential, and it is here
    // because WITHOUT it the `flip` branch of `subresultant::resultant` is
    // dead under test. Every differential comparison in this file deliberately
    // passes the higher-degree operand first, to match the convention
    // `Z3_polynomial_subresultants` reports in — which means the `(-1)^(mn)`
    // correction that `resultant` applies when its arguments arrive in the
    // other order is never executed. Measured: deleting that correction
    // outright produced ZERO divergences across the whole campaign until this
    // assertion existed. An oracle that cannot see a deleted sign correction
    // is licensing exactly the kind of unchecked work this extension is
    // supposed to prevent.
    if let (Some(r_fg), Some(r_gf)) = (ap.resultant(&aq), aq.resultant(&ap)) {
        let odd = (dp * dq) % 2 == 1;
        let expected = if odd { -r_gf.clone() } else { r_gf.clone() };
        if r_fg != expected {
            return Divergence::new(
                "psc-chain",
                "identity",
                format!(
                    "Res(p,q) = {r_fg} but Res(q,p) = {r_gf} with deg p = {dp}, deg q = {dq}; \
                     the symmetry Res(p,q) = (-1)^(deg p * deg q) Res(q,p) wants {expected}"
                ),
                inputs_z(&ap, &aq),
            );
        }
    }
    Outcome::Match(ay.len().max(1) as u64 + 1)
}

/// **Univariate discriminant**: AY's `subresultant::discriminant` against
/// `Res(f, f')` as z3 computes it.
///
/// `disc(f) = (-1)^(m(m-1)/2) * Res(f, f') / lc(f)`. z3 supplies `Res(f, f')`
/// as `psc_0` of the pair, so the identity is checked end to end without ever
/// asking z3 for a discriminant it does not export.
pub(crate) fn check_discriminant(z3: &Z3, p: &GenPoly, sab: Sabotage) -> Outcome {
    let Some((ap, pr)) = integral_coeffs(p) else {
        return Outcome::Skipped("zero polynomial");
    };
    let Some(m) = ap.degree() else {
        return Outcome::Skipped("zero polynomial");
    };
    if m < 2 || m > 7 {
        return Outcome::Skipped("degree out of range");
    }
    let Some(disc) = ap.discriminant() else {
        return Outcome::Declined("discriminant");
    };
    let disc = if sab.on() { disc + BigInt::one() } else { disc };

    // f' as rationals, for z3.
    let dr: Vec<BigRational> = pr
        .iter()
        .enumerate()
        .skip(1)
        .map(|(i, c)| c * BigRational::from(BigInt::from(i)))
        .collect();
    if dr.iter().all(Zero::is_zero) {
        return Outcome::Skipped("vanishing derivative");
    }
    // `deg f > deg f'`, so (f, f') is already z3's higher-degree-first order.
    let Some(res) = z3_resultant(z3, &pr, &dr) else {
        return Outcome::Skipped("z3 declined");
    };
    let lc = ap.coeffs().last().cloned().unwrap_or_else(BigInt::one);
    let sign_negative = (m * (m - 1) / 2) % 2 == 1;
    // Compare via multiplication so no exact-division convention enters:
    //   disc * lc == (-1)^(m(m-1)/2) * Res
    let lhs = &disc * &lc;
    let rhs = if sign_negative {
        -res.clone()
    } else {
        res.clone()
    };
    if lhs != rhs {
        return Divergence::new(
            "discriminant",
            "z3",
            format!(
                "AY disc = {disc}, lc = {lc}, so disc*lc = {lhs}; z3 gives Res(f,f') = {res} \
                 and the sign convention wants {rhs} (deg {m})"
            ),
            vec![
                ("f".to_string(), render_ints(&ap.coeffs())),
                ("shape".to_string(), p.shape.name().to_string()),
            ],
        );
    }
    Outcome::Match(1)
}

/// **PRS vs determinant**: the module's two independent chain implementations
/// against each other.
///
/// Not a z3 differential — an internal consistency check, reported with
/// reference `"identity"`. It is worth running because `subresultant_chain_prs`
/// is the fast path every caller takes while `subresultant_chain_det` is the
/// definition; if they disagree, one of them is wrong no matter what z3 says,
/// and z3 only ever observes the psc's, never the full chain polynomials.
pub(crate) fn check_chain_agreement(p: &GenPoly, q: &GenPoly, sab: Sabotage) -> Outcome {
    let (Some((ap, _)), Some((aq, _))) = (integral_coeffs(p), integral_coeffs(q)) else {
        return Outcome::Skipped("zero polynomial");
    };
    let (Some(dp), Some(dq)) = (ap.degree(), aq.degree()) else {
        return Outcome::Skipped("zero polynomial");
    };
    let (hi, lo) = if dp >= dq { (dp, dq) } else { (dq, dp) };
    // The PRS recurrence is only defined for deg f > deg g >= 1.
    if lo < 1 || hi <= lo || hi + lo > 12 {
        return Outcome::Skipped("PRS preconditions not met");
    }
    let Some(prs) = ap.subresultant_chain_prs(&aq) else {
        return Outcome::Declined("subresultant_chain_prs");
    };
    let Some(det) = ap.subresultant_chain_det(&aq) else {
        return Outcome::Declined("subresultant_chain_det");
    };
    // The two functions are indexed DIFFERENTLY, and comparing their raw
    // lengths is a harness bug, not an AY bug: `subresultant_chain_prs` returns
    // `S_0 ..= S_{deg f}` (length `deg f + 1`) because it carries the
    // normalization seeds `S_{deg f} = f` and `S_{deg f - 1} = g`, while
    // `subresultant_chain_det` returns `S_0 .. S_{deg g}` (length `deg g`).
    // Only the overlap `j < deg g` is claimed to coincide, and only that is
    // compared here.
    let n = det.len();
    if prs.len() < n {
        return Divergence::new(
            "subresultant-chain-agreement",
            "identity",
            format!(
                "PRS chain has {} entries, too short to cover S_0..S_{}",
                prs.len(),
                n - 1
            ),
            inputs_z(&ap, &aq),
        );
    }
    let mut prs: Vec<Vec<BigInt>> = prs.into_iter().take(n).collect();
    if sab.on() {
        // Drop a chain entry — the "missing rung" defect class.
        if let Some(first_non_empty) = prs.iter().position(|s| !s.is_empty()) {
            prs[first_non_empty].clear();
        } else if let Some(first) = prs.first_mut() {
            first.push(BigInt::one());
        } else {
            return Outcome::Skipped("empty chain overlap");
        }
    }
    for (j, (a, b)) in prs.iter().zip(det.iter()).enumerate() {
        if a != b {
            return Divergence::new(
                "subresultant-chain-agreement",
                "identity",
                format!(
                    "S_{j} differs: PRS [{}] vs determinant [{}]",
                    render_ints(a),
                    render_ints(b)
                ),
                inputs_z(&ap, &aq),
            );
        }
    }
    Outcome::Match(prs.len() as u64)
}

fn inputs_z(p: &OZPoly, q: &OZPoly) -> Vec<(String, String)> {
    vec![
        ("p".to_string(), render_ints(&p.coeffs())),
        ("q".to_string(), render_ints(&q.coeffs())),
    ]
}

// ============================================================================
// Bivariate
// ============================================================================

/// A generated bivariate polynomial, kept alongside its own rendering so a
/// divergence dump is reproducible without re-running the RNG.
pub(crate) struct GenBi {
    /// `x`-coefficients, low-to-high, each a list of `(y-exponent, coeff)`.
    pub(crate) x_coeffs: Vec<Vec<(u32, BigInt)>>,
}

impl GenBi {
    fn to_poly(&self) -> OBiPoly {
        OBiPoly::from_x_coeffs(&self.x_coeffs)
    }

    fn render(&self) -> String {
        let mut parts: Vec<String> = Vec::new();
        for (i, terms) in self.x_coeffs.iter().enumerate() {
            if terms.is_empty() {
                continue;
            }
            let c = terms
                .iter()
                .map(|(e, c)| {
                    if *e == 0 {
                        c.to_string()
                    } else {
                        format!("{c}*y^{e}")
                    }
                })
                .collect::<Vec<_>>()
                .join(" + ");
            parts.push(format!("({c})*x^{i}"));
        }
        if parts.is_empty() {
            "0".to_string()
        } else {
            parts.join(" + ")
        }
    }
}

/// Generate a bivariate polynomial.
///
/// The `y`-degree distribution is deliberately skewed toward 0 and 1: a
/// coefficient ring element of high degree makes every `exact_div` in the PRS
/// expensive without making it more likely to be wrong, and constant
/// coefficients are what make the leading coefficient survive specialization so
/// the case is actually comparable.
pub(crate) fn gen_bivariate(rng: &mut Rng) -> GenBi {
    let deg_x =
        usize::try_from(rng.range(1, i64::try_from(MAX_BI_DEG_X).unwrap_or(4))).unwrap_or(1);
    let mut x_coeffs: Vec<Vec<(u32, BigInt)>> = Vec::with_capacity(deg_x + 1);
    for i in 0..=deg_x {
        // The leading x-coefficient is biased toward a non-zero constant so the
        // degree-preservation side condition holds often enough to measure.
        let deg_y = if i == deg_x && rng.chance(1, 2) {
            0
        } else {
            usize::try_from(rng.range(0, i64::try_from(MAX_BI_DEG_Y).unwrap_or(3))).unwrap_or(0)
        };
        let mut terms: Vec<(u32, BigInt)> = Vec::new();
        for e in 0..=deg_y {
            if e < deg_y && rng.chance(1, 3) {
                continue;
            }
            let c = rng.range(-6, 6);
            if c == 0 {
                continue;
            }
            terms.push((u32::try_from(e).unwrap_or(0), BigInt::from(c)));
        }
        if i == deg_x && terms.is_empty() {
            terms.push((0, BigInt::one()));
        }
        x_coeffs.push(terms);
    }
    GenBi { x_coeffs }
}

/// **Bivariate psc chain**, by specialization.
///
/// AY computes the chain over `Z[y]`; each entry is then evaluated at `y = c`
/// and compared against the chain z3 computes for the specialized univariate
/// pair. Skipped unless the specialization preserves both `x`-degrees, which is
/// the precondition for subresultants to commute with it.
pub(crate) fn check_bivariate_psc(
    z3: &Z3,
    f: &GenBi,
    g: &GenBi,
    c: &BigInt,
    sab: Sabotage,
) -> Outcome {
    let (bf, bg) = (f.to_poly(), g.to_poly());
    let (Some(df), Some(dg)) = (bf.degree_x(), bg.degree_x()) else {
        return Outcome::Skipped("zero polynomial");
    };
    if df < 1 || dg < 1 {
        return Outcome::Skipped("degree < 1");
    }
    // Degree preservation: the theorem's side condition.
    let lc_ok = |b: &OBiPoly| -> bool {
        b.leading_x()
            .map(|l: OYPoly| !l.eval_at(c).is_zero())
            .unwrap_or(false)
    };
    if !lc_ok(&bf) || !lc_ok(&bg) {
        return Outcome::Skipped("specialization drops the x-degree");
    }
    let Some(chain) = bf.psc_chain(&bg) else {
        return Outcome::Declined("bivariate psc_chain");
    };
    let mut specialized: Vec<BigInt> = chain.iter().map(|e| e.eval_at(c)).collect();
    if sab.on() {
        if let Some(last) = specialized.iter_mut().rev().find(|v| !v.is_zero()) {
            *last = -last.clone();
        } else {
            specialized.push(BigInt::one());
        }
    }
    let ay: Vec<BigInt> = specialized
        .iter()
        .filter(|v| !v.is_zero())
        .cloned()
        .collect();

    // z3 side: the SPECIALIZED univariate pair.
    let sf = bf.specialize(c);
    let sg = bg.specialize(c);
    let to_rats = |p: &OZPoly| -> Vec<BigRational> {
        p.coeffs().into_iter().map(BigRational::from).collect()
    };
    let (fr, gr) = (to_rats(&sf), to_rats(&sg));
    let Some(raw) = z3_chain_ints(z3, &fr, &gr) else {
        return Outcome::Skipped("z3 declined");
    };
    if raw.is_empty() {
        return Outcome::Skipped("empty subresultant chain");
    }
    let want = z3_nonzero_chain(&raw);

    if ay != want {
        return Divergence::new(
            "bivariate-psc",
            "z3",
            format!(
                "at y = {c}: AY's specialized psc chain [{}] but z3's chain for the \
                 specialized pair is [{}] (AY full specialized chain [{}])",
                render_ints(&ay),
                render_ints(&want),
                render_ints(&specialized),
            ),
            inputs_bi(f, g, c, &sf, &sg),
        );
    }
    Outcome::Match(ay.len().max(1) as u64)
}

/// **Bivariate resultant**, by specialization: `Res_x(F, G)(c)` against z3's
/// resultant of the specialized pair.
pub(crate) fn check_bivariate_resultant(
    z3: &Z3,
    f: &GenBi,
    g: &GenBi,
    c: &BigInt,
    sab: Sabotage,
) -> Outcome {
    let (bf, bg) = (f.to_poly(), g.to_poly());
    let (Some(df), Some(dg)) = (bf.degree_x(), bg.degree_x()) else {
        return Outcome::Skipped("zero polynomial");
    };
    if df < 1 || dg < 1 {
        return Outcome::Skipped("degree < 1");
    }
    let lc_ok = |b: &OBiPoly| -> bool {
        b.leading_x()
            .map(|l: OYPoly| !l.eval_at(c).is_zero())
            .unwrap_or(false)
    };
    if !lc_ok(&bf) || !lc_ok(&bg) {
        return Outcome::Skipped("specialization drops the x-degree");
    }
    // Argument order is load-bearing and the two sides do NOT agree on it.
    // `subresultant::resultant` normalizes internally and applies the
    // `(-1)^(mn)` correction, so it returns the true ordered `Res(F, G)`;
    // `Z3_polynomial_subresultants` reports `psc_0` of (higher-degree,
    // lower-degree) with no such correction. Passing the higher-degree operand
    // first makes AY's correction a no-op and puts both sides in z3's
    // convention. Omitting this reports a sign divergence on every pair whose
    // degrees are in the "wrong" order with `deg F * deg G` odd — correct code,
    // fictional bug.
    let (rf, rg) = if df >= dg { (&bf, &bg) } else { (&bg, &bf) };
    let Some(res) = rf.resultant(rg) else {
        return Outcome::Declined("bivariate resultant");
    };
    let mut val = res.eval_at(c);
    if sab.on() {
        val += BigInt::one();
    }

    let sf = bf.specialize(c);
    let sg = bg.specialize(c);
    let to_rats = |p: &OZPoly| -> Vec<BigRational> {
        p.coeffs().into_iter().map(BigRational::from).collect()
    };
    // Order the specialized pair the same way, so both sides stay in z3's
    // higher-degree-first convention.
    let (zf, zg) = if df >= dg {
        (to_rats(&sf), to_rats(&sg))
    } else {
        (to_rats(&sg), to_rats(&sf))
    };
    let Some(z3_res) = z3_resultant(z3, &zf, &zg) else {
        return Outcome::Skipped("z3 declined");
    };
    if val != z3_res {
        return Divergence::new(
            "bivariate-resultant",
            "z3",
            format!(
                "at y = {c}: AY's Res_x(F,G) specializes to {val}, z3 gives {z3_res} \
                 for the specialized pair"
            ),
            inputs_bi(f, g, c, &sf, &sg),
        );
    }
    Outcome::Match(1)
}

fn inputs_bi(f: &GenBi, g: &GenBi, c: &BigInt, sf: &OZPoly, sg: &OZPoly) -> Vec<(String, String)> {
    vec![
        ("F".to_string(), f.render()),
        ("G".to_string(), g.render()),
        ("y".to_string(), c.to_string()),
        ("F(x,y0)".to_string(), render_ints(&sf.coeffs())),
        ("G(x,y0)".to_string(), render_ints(&sg.coeffs())),
    ]
}
