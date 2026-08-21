// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Differential checks for `crates/ay-theories/nra/src/mroot.rs` — real-root
//! isolation of a MULTIVARIATE polynomial at an algebraic sample point.
//!
//! # Why these are the strongest checks in the oracle
//!
//! Every other comparison in this binary is indirect. The univariate checks
//! compare AY against a z3 primitive that answers a NEARBY question; the
//! bivariate subresultant checks compare AY's multivariate answer against z3's
//! univariate one through a specialization theorem, because z3's C API will
//! not hand back a multivariate subresultant in a form an oracle can read
//! without writing its own normalizer.
//!
//! Here there is no gap at all. `Z3_algebraic_roots(c, p, n, a)` is a thin
//! wrapper (`api/api_algebraic.cpp:352`) around
//!
//! ```text
//!     algebraic_numbers::manager::isolate_roots(p, x2v, roots)
//! ```
//!
//! and `Z3_algebraic_eval(c, p, n, a)` around `eval_sign_at(p, x2v)` — the two
//! functions `mroot.rs` reimplements, called with the same polynomial and the
//! same sample point. The reference is answering the identical question.
//!
//! # How the sample point is agreed on without sharing a representation
//!
//! Neither side is told the other's algebraic numbers. Both are given the same
//! DEFINING POLYNOMIAL and the same ROOT INDEX:
//!
//! * AY isolates that polynomial's real roots with its own univariate
//!   machinery and takes the `i`-th ascending one;
//! * z3 is asked for the same polynomial's roots via `Z3_algebraic_roots` with
//!   no assignment, and the `i`-th ascending one is used.
//!
//! If the two lists differ in length the case is SKIPPED, not diverged — that
//! is the univariate `roots` check's business and reporting it here would
//! double-count one bug as two.
//!
//! Answers are then compared through [`crate::z3::Z3::bracket`], which turns a
//! z3 algebraic number into a rational enclosure using z3's own exact
//! comparisons, and AY's exact `cmp_rational` decides whether its root lies
//! inside. No representation, no floating point, and no normalizer is shared.
//!
//! # What the generator deliberately reaches
//!
//! Random polynomials never trigger `mroot.rs`'s hardest branch: the
//! VANISHING RESULTANT, which needs the polynomial and the coordinate's
//! defining polynomial to share a factor. One generated shape forces it —
//! a linear factor `(y - c)` is multiplied into BOTH — so the escape path
//! (fresh variable bound to the leading coefficient's value, recursive call)
//! is exercised against z3 rather than only against unit tests.

use std::cmp::Ordering;

use ay_nra::oracle_api::{OAlg, OAnum, OMPoly, OPoly, ORoot, OVar2Anum};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;

use crate::checks::{Divergence, Outcome, Sabotage};
use crate::polygen::Rng;
use crate::z3::{Ptr, Z3};

/// Bisection steps used to bracket a z3 root before comparing it to AY's.
///
/// `40` puts the enclosure at `2^-40` of its initial width, far below any
/// separation these degrees produce, so a containment result is an equality
/// result in practice — and a genuinely equal pair can never fail it, since
/// AY's root is exactly inside every enclosure of itself.
const BRACKET_STEPS: u32 = 40;

/// Maximum degree of a coordinate's defining polynomial.
///
/// The elimination multiplies degrees: with `k` assigned coordinates of degree
/// `d` and an unknown of degree `e`, the resultant chain reaches `e * d^k`.
/// At `3` and two coordinates that is a degree-27 univariate isolation per
/// case, which is measured at milliseconds; at `5` it is degree-125 and the
/// case time is dominated by `BigRational` Sturm sequences rather than by
/// anything either implementation gets wrong.
const MAX_DEF_DEG: usize = 3;

/// Maximum degree of the generated polynomial in the unknown.
const MAX_X_DEG: usize = 3;

/// Maximum degree of the generated polynomial in any assigned coordinate.
const MAX_Y_DEG: usize = 2;

/// Work budget for one multivariate case, in units of the degree of the
/// univariate polynomial the elimination produces:
/// `deg_x(p) * prod_i deg(m_i)` (see [`GenMv::elimination_degree`]).
///
/// MEASURED, not guessed. At seed 5 without this guard, case #47 — two
/// coordinates of defining degree 3 and 4 against a cubic in `x`, an
/// elimination degree of 36 — ran for **32.97 s**, entirely inside AY (z3
/// answered promptly), and dominated a 400-case run whose other 399 cases took
/// 41 s together. The cost is AY's own known heavy tail: `isolate_roots` on
/// the eliminated polynomial runs a `BigRational` Sturm sequence whose
/// coefficients are the resultant's, and both degree and bit-width grow
/// multiplicatively through the chain.
///
/// At `24` the measured worst mv case is under a second. Raising it does not
/// reach any new BRANCH of `mroot.rs` — every path is already covered at lower
/// degree, and the unit tests pin the degenerate ones — it only buys larger
/// numbers through the same code, at a cost that would consume the campaign.
/// A case over budget is reported as inapplicable, never silently dropped.
const MAX_ELIM_DEGREE: usize = 24;

// ---------------------------------------------------------------------------
// Generated case
// ---------------------------------------------------------------------------

/// One multivariate case: a sample point given by defining polynomials and
/// root indices, plus a polynomial over those coordinates and the unknown.
pub(crate) struct GenMv {
    /// Defining polynomial for each coordinate `0 .. nvars`, low-to-high.
    pub(crate) defs: Vec<Vec<BigRational>>,
    /// Which ascending root of `defs[i]` this coordinate takes.
    pub(crate) picks: Vec<usize>,
    /// `(exponent vector over vars 0 ..= nvars, coefficient)`.
    pub(crate) terms: Vec<(Vec<u32>, BigInt)>,
    /// Number of ASSIGNED coordinates. The unknown is variable `nvars`.
    pub(crate) nvars: usize,
    /// Which generator shape produced this case.
    pub(crate) shape: &'static str,
}

impl GenMv {
    /// Degree of the univariate polynomial the elimination chain produces:
    /// each coordinate `i` is eliminated by a resultant against a defining
    /// polynomial of degree `deg(m_i)`, which multiplies the degree in the
    /// unknown by that much.
    ///
    /// `n` is how many coordinates the check actually assigns — the
    /// root-isolation checks assign `nvars`, the sign check assigns all of
    /// them.
    pub(crate) fn elimination_degree(&self, n: usize) -> usize {
        let x_deg = self
            .terms
            .iter()
            .map(|(e, _)| e.get(self.nvars).copied().unwrap_or(0) as usize)
            .max()
            .unwrap_or(0);
        let mut cost = x_deg.max(1);
        for d in self.defs.iter().take(n) {
            cost = cost.saturating_mul(d.len().saturating_sub(1).max(1));
        }
        cost
    }
}

fn small_int(rng: &mut Rng) -> BigInt {
    BigInt::from(rng.range(-4, 4))
}

fn nonzero_small_int(rng: &mut Rng) -> BigInt {
    let mut c = small_int(rng);
    if c.is_zero() {
        c = BigInt::from(1);
    }
    c
}

fn rat(c: &BigInt) -> BigRational {
    BigRational::from_integer(c.clone())
}

/// Coefficients of `sum_i c_i y^i` with a non-zero leading coefficient.
fn gen_def_poly(rng: &mut Rng) -> Vec<BigInt> {
    let deg = 1 + usize::try_from(rng.below(MAX_DEF_DEG as u64)).unwrap_or(0);
    let mut coeffs: Vec<BigInt> = (0..deg).map(|_| small_int(rng)).collect();
    coeffs.push(nonzero_small_int(rng));
    coeffs
}

/// Multiply two integer coefficient vectors.
fn mul_ints(a: &[BigInt], b: &[BigInt]) -> Vec<BigInt> {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    let mut out = vec![BigInt::from(0); a.len() + b.len() - 1];
    for (i, x) in a.iter().enumerate() {
        for (j, y) in b.iter().enumerate() {
            out[i + j] += x * y;
        }
    }
    out
}

/// Generate a case. Three shapes:
///
/// * `plain` — an unstructured polynomial over the coordinates. This is the
///   ordinary path: resultant elimination, univariate isolation, sieve.
/// * `conjugate-bait` — `p` is `x - y_0`, whose resultant against `y_0`'s
///   defining polynomial has a root for EVERY conjugate of `y_0`, of which
///   exactly one is a real root of `p` at the sample point. A missing sieve
///   shows up immediately.
/// * `shared-factor` — a linear factor `(y_0 - c)` is multiplied into both `p`
///   and `y_0`'s defining polynomial, so `Res_{y_0}(p, m_0)` vanishes
///   identically and the escape path is the only way to an answer.
pub(crate) fn gen_mv(rng: &mut Rng) -> GenMv {
    // One or two assigned coordinates. Two is where the interesting work is
    // (successive resultants, a separation bound over several coordinates),
    // but it is also where the degrees multiply, so it is the minority.
    let nvars = if rng.chance(1, 3) { 2 } else { 1 };
    let shape_roll = rng.below(10);

    let mut defs: Vec<Vec<BigInt>> = (0..=nvars).map(|_| gen_def_poly(rng)).collect();

    let (terms, shape) = if shape_roll < 2 {
        // conjugate-bait: x - y_0
        (
            vec![
                (vec![0; nvars + 1].with_at(nvars, 1), BigInt::from(1)),
                (vec![0; nvars + 1].with_at(0, 1), BigInt::from(-1)),
            ],
            "conjugate-bait",
        )
    } else if shape_roll < 5 {
        // shared-factor: (y_0 - c) * (a*x^2 + b*x + d), with (y_0 - c) also
        // multiplied into y_0's own defining polynomial.
        let c = small_int(rng);
        let linear = vec![-c.clone(), BigInt::from(1)];
        defs[0] = mul_ints(&defs[0], &linear);
        let a = nonzero_small_int(rng);
        let b = small_int(rng);
        let d = small_int(rng);
        // (y_0 - c) * (a x^2 + b x + d)
        let mut terms: Vec<(Vec<u32>, BigInt)> = Vec::new();
        for (xe, coeff) in [(2u32, a), (1, b), (0, d)] {
            if coeff.is_zero() {
                continue;
            }
            terms.push((
                vec![0; nvars + 1].with_at(0, 1).with_at(nvars, xe),
                coeff.clone(),
            ));
            terms.push((vec![0; nvars + 1].with_at(nvars, xe), -(&c * &coeff)));
        }
        (terms, "shared-factor")
    } else {
        // plain
        let nterms = 2 + usize::try_from(rng.below(4)).unwrap_or(0);
        let mut terms: Vec<(Vec<u32>, BigInt)> = Vec::new();
        for _ in 0..nterms {
            let mut exps = vec![0u32; nvars + 1];
            for e in exps.iter_mut().take(nvars) {
                *e = u32::try_from(rng.below(MAX_Y_DEG as u64 + 1)).unwrap_or(0);
            }
            exps[nvars] = u32::try_from(rng.below(MAX_X_DEG as u64 + 1)).unwrap_or(0);
            terms.push((exps, small_int(rng)));
        }
        // Guarantee the unknown actually appears, so the case is not a
        // degenerate "no roots by construction".
        terms.push((vec![0; nvars + 1].with_at(nvars, 1), nonzero_small_int(rng)));
        (terms, "plain")
    };

    GenMv {
        defs: defs.iter().map(|d| d.iter().map(rat).collect()).collect(),
        picks: (0..=nvars)
            .map(|_| usize::try_from(rng.next_u64() % 8).unwrap_or(0))
            .collect(),
        terms,
        nvars,
        shape,
    }
}

/// `vec.with_at(i, v)` — small helper so the shape tables above read as
/// exponent vectors instead of five lines of mutation each.
trait WithAt {
    fn with_at(self, i: usize, v: u32) -> Self;
}

impl WithAt for Vec<u32> {
    fn with_at(mut self, i: usize, v: u32) -> Self {
        self[i] = v;
        self
    }
}

// ---------------------------------------------------------------------------
// Building the shared sample point
// ---------------------------------------------------------------------------

/// One coordinate, as both sides see it.
struct Coord {
    ay: OAnum,
    z3: Ptr,
}

/// Build coordinate `i`: AY isolates `def`'s roots itself, z3 isolates the
/// same polynomial's roots, and the `pick`-th ascending root of each is the
/// shared value. Returns `Err(outcome)` when the case cannot be built.
fn build_coord(z3: &Z3, def: &[BigRational], pick: usize) -> Result<Coord, Outcome> {
    let ap = OPoly::from_coeffs(def.to_vec());
    if ap.degree().unwrap_or(0) < 1 {
        return Err(Outcome::Skipped("degenerate defining polynomial"));
    }
    let Some(sf) = ap.square_free_part() else {
        return Err(Outcome::Declined("square_free_part"));
    };
    let Some(markers) = sf.isolate_roots() else {
        return Err(Outcome::Declined("isolate_roots"));
    };
    if markers.is_empty() {
        return Err(Outcome::Skipped("coordinate has no real roots"));
    }
    let Some(zroots) = z3.roots(def) else {
        return Err(Outcome::Skipped("z3 declined the coordinate"));
    };
    if zroots.len() != markers.len() {
        // The `roots` check owns this disagreement.
        return Err(Outcome::Skipped("coordinate root counts differ"));
    }
    let idx = pick % markers.len();
    let ay = match &markers[idx] {
        ORoot::Rational(r) => OAnum::rational(r.clone()),
        ORoot::Interval(lo, hi) => {
            let Some(alpha) = OAlg::new(&sf, lo, hi) else {
                return Err(Outcome::Declined("OAlg::new"));
            };
            OAnum::algebraic(&alpha)
        }
    };
    Ok(Coord {
        ay,
        z3: zroots[idx],
    })
}

/// Build every coordinate `0 .. n`.
fn build_coords(z3: &Z3, g: &GenMv, n: usize) -> Result<Vec<Coord>, Outcome> {
    let mut out = Vec::with_capacity(n);
    for i in 0..n {
        out.push(build_coord(z3, &g.defs[i], g.picks[i])?);
    }
    Ok(out)
}

/// AY's polynomial and z3's AST for the same terms.
fn build_poly(z3: &Z3, g: &GenMv) -> Option<(OMPoly, Ptr)> {
    let ay = OMPoly::from_terms(&g.terms);
    if ay.is_zero() {
        return None;
    }
    let zterms: Vec<(Vec<u32>, BigRational)> =
        g.terms.iter().map(|(e, c)| (e.clone(), rat(c))).collect();
    let zp = z3.mpoly_bound(&zterms)?;
    Some((ay, zp))
}

/// Does AY's root `ay` agree with z3's root `v`?
///
/// `None` when either side declines. The z3 side is bracketed with z3's own
/// exact comparisons; AY's exact comparison then decides containment.
fn agrees(z3: &Z3, v: Ptr, ay: &OAnum) -> Option<bool> {
    let (lo, hi) = z3.bracket(v, BRACKET_STEPS)?;
    if lo == hi {
        return Some(ay.cmp_rational(&lo)? == Ordering::Equal);
    }
    Some(ay.cmp_rational(&lo)? == Ordering::Greater && ay.cmp_rational(&hi)? == Ordering::Less)
}

fn inputs(g: &GenMv) -> Vec<(String, String)> {
    let mut out = vec![
        ("shape".to_string(), g.shape.to_string()),
        ("assigned coordinates".to_string(), g.nvars.to_string()),
        ("p".to_string(), render_terms(&g.terms)),
    ];
    for (i, d) in g.defs.iter().enumerate() {
        out.push((
            format!("def(x{i}) [root #{}]", g.picks[i]),
            crate::polygen::render(d),
        ));
    }
    out
}

fn render_terms(terms: &[(Vec<u32>, BigInt)]) -> String {
    let mut parts: Vec<String> = Vec::new();
    for (exps, c) in terms {
        if c.is_zero() {
            continue;
        }
        let mut s = c.to_string();
        for (v, &e) in exps.iter().enumerate() {
            if e == 1 {
                s.push_str(&format!("*x{v}"));
            } else if e > 1 {
                s.push_str(&format!("*x{v}^{e}"));
            }
        }
        parts.push(s);
    }
    if parts.is_empty() {
        "0".to_string()
    } else {
        parts.join(" + ")
    }
}

// ---------------------------------------------------------------------------
// The checks
// ---------------------------------------------------------------------------

/// `mroot::isolate_roots_at` vs `Z3_algebraic_roots`.
pub(crate) fn check_mv_roots(z3: &Z3, g: &GenMv, sab: Sabotage) -> Outcome {
    if g.elimination_degree(g.nvars) > MAX_ELIM_DEGREE {
        return Outcome::Skipped("elimination degree over budget");
    }
    let coords = match build_coords(z3, g, g.nvars) {
        Ok(c) => c,
        Err(o) => return o,
    };
    let Some((ap, zp)) = build_poly(z3, g) else {
        return Outcome::Skipped("degenerate polynomial");
    };
    let x = u32::try_from(g.nvars).unwrap_or(0);
    if ap.degree_in(x) == 0 {
        return Outcome::Skipped("unknown does not occur");
    }

    let mut x2v = OVar2Anum::new();
    for (i, c) in coords.iter().enumerate() {
        x2v.set(u32::try_from(i).unwrap_or(0), &c.ay);
    }
    let Some(mut ay_roots) = ap.isolate_roots_at(x, &x2v) else {
        return Outcome::Declined("isolate_roots_at");
    };
    let values: Vec<Ptr> = coords.iter().map(|c| c.z3).collect();
    let Some(z3_roots) = z3.roots_at(zp, &values) else {
        return Outcome::Skipped("z3 declined isolate_roots");
    };

    // Sabotage: drop a root, or invent one when there are none to drop.
    if sab.on() {
        if ay_roots.is_empty() {
            ay_roots.push(OAnum::rational(BigRational::new(
                BigInt::from(1),
                BigInt::from(2),
            )));
        } else {
            ay_roots.pop();
        }
    }

    if ay_roots.len() != z3_roots.len() {
        return Divergence::new(
            "mv-isolate-roots",
            "z3",
            format!(
                "AY found {} root(s) at the sample point, z3 found {}",
                ay_roots.len(),
                z3_roots.len()
            ),
            inputs(g),
        );
    }
    let mut comparisons = 1u64;
    for (i, (v, a)) in z3_roots.iter().zip(&ay_roots).enumerate() {
        let Some(ok) = agrees(z3, *v, a) else {
            return Outcome::Declined("root comparison");
        };
        comparisons += 1;
        if !ok {
            return Divergence::new(
                "mv-isolate-roots",
                "z3",
                format!(
                    "root #{} disagrees: z3 says {}, AY's value is not in that enclosure",
                    i + 1,
                    z3.ast_string(*v)
                ),
                inputs(g),
            );
        }
    }
    Outcome::Match(comparisons)
}

/// `mroot::eval_sign_at` vs `Z3_algebraic_eval`.
///
/// Every coordinate INCLUDING the last is assigned here, which is what
/// `Z3_algebraic_eval` requires: it refuses a polynomial whose maximal
/// variable is at or past the number of values supplied.
pub(crate) fn check_mv_sign_at(z3: &Z3, g: &GenMv, sab: Sabotage) -> Outcome {
    let n = g.nvars + 1;
    if g.elimination_degree(n) > MAX_ELIM_DEGREE {
        return Outcome::Skipped("elimination degree over budget");
    }
    let coords = match build_coords(z3, g, n) {
        Ok(c) => c,
        Err(o) => return o,
    };
    let Some((ap, zp)) = build_poly(z3, g) else {
        return Outcome::Skipped("degenerate polynomial");
    };
    let mut x2v = OVar2Anum::new();
    for (i, c) in coords.iter().enumerate() {
        x2v.set(u32::try_from(i).unwrap_or(0), &c.ay);
    }
    let Some(ay_sign) = ap.eval_sign_at(&x2v) else {
        return Outcome::Declined("eval_sign_at");
    };
    let values: Vec<Ptr> = coords.iter().map(|c| c.z3).collect();
    let Some(z3_sign) = z3.eval_sign_at(zp, &values) else {
        return Outcome::Skipped("z3 declined eval_sign");
    };
    // Sabotage: turn a zero into a positive, and flip everything else. The
    // zero case is the one that matters — it is the sieve's decision.
    let ay_sign = if sab.on() {
        if ay_sign == 0 {
            1
        } else {
            -ay_sign
        }
    } else {
        ay_sign
    };
    if ay_sign != z3_sign {
        return Divergence::new(
            "mv-sign-at",
            "z3",
            format!("AY's sign is {ay_sign}, z3's is {z3_sign}"),
            inputs(g),
        );
    }
    Outcome::Match(1)
}

/// `mroot::isolate_roots_closest_at` vs the same selection made from z3's FULL
/// root list using z3's own exact comparisons.
///
/// The selection rule is the one z3's header states for
/// `isolate_roots_closest`: the last root `<= s`, the first root `> s`, or the
/// single root `s` when `s` is itself a root.
pub(crate) fn check_mv_closest(z3: &Z3, g: &GenMv, s: &BigRational, sab: Sabotage) -> Outcome {
    if g.elimination_degree(g.nvars) > MAX_ELIM_DEGREE {
        return Outcome::Skipped("elimination degree over budget");
    }
    let coords = match build_coords(z3, g, g.nvars) {
        Ok(c) => c,
        Err(o) => return o,
    };
    let Some((ap, zp)) = build_poly(z3, g) else {
        return Outcome::Skipped("degenerate polynomial");
    };
    let x = u32::try_from(g.nvars).unwrap_or(0);
    if ap.degree_in(x) == 0 {
        return Outcome::Skipped("unknown does not occur");
    }
    let mut x2v = OVar2Anum::new();
    for (i, c) in coords.iter().enumerate() {
        x2v.set(u32::try_from(i).unwrap_or(0), &c.ay);
    }
    let values: Vec<Ptr> = coords.iter().map(|c| c.z3).collect();
    let Some(z3_roots) = z3.roots_at(zp, &values) else {
        return Outcome::Skipped("z3 declined isolate_roots");
    };

    // z3's side of the selection, decided entirely by z3's comparisons.
    let s_ast = z3.rational(s);
    let mut expect: Vec<usize> = Vec::new();
    let mut below: Option<usize> = None;
    let mut above: Option<usize> = None;
    let mut exact: Option<usize> = None;
    for (i, v) in z3_roots.iter().enumerate() {
        if z3.eq(*v, s_ast) {
            exact = Some(i);
            break;
        }
        if z3.lt(*v, s_ast) {
            below = Some(i);
        } else if above.is_none() {
            above = Some(i);
        }
    }
    if z3.errored() {
        return Outcome::Skipped("z3 errored while ordering roots");
    }
    if let Some(i) = exact {
        expect.push(i);
    } else {
        expect.extend(below);
        expect.extend(above);
    }

    let Some((mut ay_roots, mut ay_idx)) = ap.isolate_roots_closest_at(x, &x2v, s) else {
        return Outcome::Declined("isolate_roots_closest_at");
    };
    if sab.on() {
        if ay_roots.is_empty() {
            ay_roots.push(OAnum::rational(s.clone()));
            ay_idx.push(1);
        } else {
            ay_roots.pop();
            ay_idx.pop();
        }
    }

    if ay_idx.len() != expect.len() {
        return Divergence::new(
            "mv-closest-roots",
            "z3",
            format!(
                "around s = {s}, AY returned {} root(s), z3's list selects {}",
                ay_idx.len(),
                expect.len()
            ),
            inputs(g),
        );
    }
    let mut comparisons = 1u64;
    for (k, &i) in expect.iter().enumerate() {
        // 1-based index into the full ascending list.
        if ay_idx[k] != i + 1 {
            return Divergence::new(
                "mv-closest-roots",
                "z3",
                format!(
                    "around s = {s}, AY's selected root #{} has index {}, z3's has {}",
                    k + 1,
                    ay_idx[k],
                    i + 1
                ),
                inputs(g),
            );
        }
        comparisons += 1;
        let Some(ok) = agrees(z3, z3_roots[i], &ay_roots[k]) else {
            return Outcome::Declined("root comparison");
        };
        comparisons += 1;
        if !ok {
            return Divergence::new(
                "mv-closest-roots",
                "z3",
                format!(
                    "around s = {s}, AY's selected root #{} is not z3's {}",
                    k + 1,
                    z3.ast_string(z3_roots[i])
                ),
                inputs(g),
            );
        }
    }
    Outcome::Match(comparisons)
}
