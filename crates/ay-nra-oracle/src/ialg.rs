// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Differential checks for `crates/ay-theories/nra/src/ialg.rs` — interval sets
//! whose endpoints are real algebraic numbers.
//!
//! # What z3 can be asked here, measured
//!
//! ```text
//!   $ ls reference/z3/5.0.0/                          -> bin include
//!   $ find reference/z3/5.0.0 -name '*nlsat*'         -> (nothing)
//!   $ nm -gU reference/z3/5.0.0/bin/libz3.dylib | grep -c Z3_algebraic  -> 21
//! ```
//!
//! `nlsat_interval_set.cpp` is **not present** — the distribution is binary —
//! so nothing here is compared against a transcription. What z3 does expose is
//! everything needed to compute set membership INDEPENDENTLY:
//! `Z3_algebraic_roots` for the endpoints, and `Z3_algebraic_lt/_gt/_eq` for
//! the comparisons. So for every check below the reference answer is built from
//! z3's own ordering of z3's own roots against the RAW interval list, never
//! from AY's normalised set. Normalisation — sorting with a fallible
//! comparator, merging adjacent cells, dropping empty ones — is therefore
//! itself under test: it must preserve the point set exactly.
//!
//! # The six blind-spot patterns, and what each check does about them
//!
//!   1. **An entry point no check calls.** Every public entry of the facade is
//!      called by name here: `from_parts`, `full`, `empty`, `is_empty`, `len`,
//!      `intervals`, `justification`, `contains`, `union`, `intersect`,
//!      `complement`, `subtract`, `pick`, `oialg_classify_value`,
//!      `oialg_from_sign_condition`, and the three ceiling accessors.
//!      `check_membership` asserts the roster.
//!   2. **A guard that never fires.** `check_membership` fires the
//!      closed-infinity refusal and the `MAX_INTERVALS` refusal on purpose,
//!      each paired with a positive control on the SAME endpoints, so a
//!      module that always refused would fail too.
//!   3. **A stored flag the metric is read off.** The `pick` ladder's rung is
//!      NOT stored. `pick` returns a bare value; the rung is re-derived by
//!      `oialg_classify_value` from that value alone. `check_pick` additionally
//!      searches for a simpler value ITSELF, using z3, so the minimality claim
//!      is never taken on AY's word.
//!   4. **An unwitnessed witness.** The probe list deliberately contains the
//!      ENDPOINTS themselves, as genuine algebraic numbers. Probing only at
//!      rationals can never distinguish `(a, b)` from `[a, b]`, so every
//!      strictness bug would be invisible — the questions would be ones the
//!      code cannot get wrong.
//!   5. **A pure function tested only through its consumer.**
//!      `oialg_from_sign_condition` takes the root list as an ARGUMENT rather
//!      than isolating roots itself, so `check_sign_cells` drives it directly
//!      on z3's own root list. `oialg_classify_value` is likewise called on
//!      arbitrary values, not only on `pick`'s output.
//!   6. **A fail-open predicate.** This is the one that matters. `contains`,
//!      `intersect`, `complement` and `from_sign_condition` all return
//!      `Option`, and all of them bottom out in `Anum::cmp_anum`, which is
//!      documented TOTAL below the separation ceiling. The generator keeps
//!      every input strictly under the declared ceilings and each check
//!      ASSERTS that before the call, so a `None` from any of them is reported
//!      as a **divergence**, not swallowed as a decline. Without that, the
//!      exact defect this module is most likely to grow — a comparison that
//!      cannot be decided being answered permissively — would show up as a
//!      falling match count and nothing else.

use ay_nra::oracle_api::{
    oialg_classify_value, oialg_from_sign_condition, oialg_max_intervals, oialg_max_just,
    oialg_max_simple_den, ODyadicAnum, OIAlgInterval, OIAlgSet, OIRung, OISignCond,
};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

use crate::anum::{dyadic_iv, rationals};
use crate::checks::{Divergence, Outcome, Sabotage};
use crate::polygen::Rng;
use crate::z3::{Ast, Z3};

/// Integers scanned either side of an interval when `check_pick` looks for a
/// simpler value than AY returned. Bounded so the minimality leg can never run
/// away on a wide interval; a wider interval skips the leg instead.
const MINIMALITY_SPAN: i64 = 24;

/// One generated case.
pub(crate) struct GenIA {
    /// Integer polynomial supplying the first set's endpoints.
    pub(crate) p: Vec<BigInt>,
    /// Integer polynomial supplying the second set's endpoints.
    pub(crate) q: Vec<BigInt>,
    /// Which sign condition the cell-decomposition check builds.
    pub(crate) cond: OISignCond,
    /// Extra rational probe points.
    pub(crate) points: Vec<BigRational>,
    /// Strictness bits, consumed one endpoint at a time.
    pub(crate) strict: u64,
    /// Shape label for reporting.
    pub(crate) shape: &'static str,
}

fn ints(v: &[i64]) -> Vec<BigInt> {
    v.iter().map(|&c| BigInt::from(c)).collect()
}

fn pmul(a: &[BigInt], b: &[BigInt]) -> Vec<BigInt> {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    let mut out = vec![BigInt::zero(); a.len() + b.len() - 1];
    for (i, x) in a.iter().enumerate() {
        for (j, y) in b.iter().enumerate() {
            out[i + j] += x * y;
        }
    }
    out
}

fn render(p: &[BigInt]) -> String {
    p.iter()
        .enumerate()
        .map(|(i, c)| format!("{c}*x^{i}"))
        .collect::<Vec<_>>()
        .join(" + ")
}

fn inputs(g: &GenIA) -> Vec<(String, String)> {
    vec![
        ("p".to_string(), render(&g.p)),
        ("q".to_string(), render(&g.q)),
        ("cond".to_string(), format!("{:?}", g.cond)),
        (
            "points".to_string(),
            g.points
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(","),
        ),
        ("strict".to_string(), format!("{:#018x}", g.strict)),
        ("shape".to_string(), g.shape.to_string()),
    ]
}

/// Squarefree quadratic irrationals, so endpoints are genuinely irrational and
/// no rational probe can ever coincide with one.
const IRRATIONALS: [i64; 8] = [2, 3, 5, 6, 7, 10, 11, 13];

/// Draw a case.
///
/// Five shapes, each reaching structure a uniform draw would not:
///
///   * `irrational`  — `(x^2 - d)(x^2 - e)`, four irrational roots, so a set
///     built from consecutive pairs has genuinely algebraic endpoints on both
///     ends of every interval.
///   * `shared`      — `p` and `q` share a quadratic factor, so the two sets
///     have endpoints that are EQUAL through different defining polynomials.
///     This is the only shape that reaches the equality branch of the endpoint
///     comparison, and it is what makes adjacency and empty-intersection
///     reachable at an algebraic point rather than only at a rational one.
///   * `interleaved` — `p`'s roots and `q`'s roots alternate, so the
///     intersection two-pointer scan advances each side in turn instead of
///     draining one first. With nested shapes only, the `Equal` arm of the
///     advance test is the only one exercised.
///   * `rational`    — planted rational and dyadic roots, so `pick` can reach
///     its `Integer` and `Simple` rungs and the endpoints collapse to
///     `Anum::Rational`.
///   * `dense`       — arbitrary coefficients, where degree and coefficient
///     growth actually bite.
pub(crate) fn gen_ia(rng: &mut Rng) -> GenIA {
    let shape = match rng.below(6) {
        0 => "irrational",
        1 => "shared",
        2 => "interleaved",
        3 => "rational",
        4 => "narrow",
        _ => "dense",
    };
    let d = IRRATIONALS[usize::try_from(rng.below(IRRATIONALS.len() as u64)).unwrap_or(0)];
    let e = IRRATIONALS[usize::try_from(rng.below(IRRATIONALS.len() as u64)).unwrap_or(0)];
    let quad_d = ints(&[-d, 0, 1]);
    let quad_e = ints(&[-e, 0, 1]);

    let (p, q) = match shape {
        "irrational" => (pmul(&quad_d, &quad_e), pmul(&quad_e, &ints(&[-3, 0, 1]))),
        "shared" => (
            pmul(&quad_d, &ints(&[-rng.range(-5, 5), 1])),
            pmul(&quad_d, &ints(&[-rng.range(-5, 5), 1])),
        ),
        // `(x-1)(x-3)(x-5)` against `(x-2)(x-4)(x-6)`: strictly alternating.
        "interleaved" => (
            pmul(&pmul(&ints(&[-1, 1]), &ints(&[-3, 1])), &ints(&[-5, 1])),
            pmul(&pmul(&ints(&[-2, 1]), &ints(&[-4, 1])), &ints(&[-6, 1])),
        ),
        "rational" => {
            let k = 1 + u32::try_from(rng.below(3)).unwrap_or(0);
            (
                pmul(
                    &ints(&[-rng.range(-6, 6), 1]),
                    &ints(&[-rng.range(-9, 9), 1i64 << k]),
                ),
                pmul(
                    &ints(&[-rng.range(-6, 6), 1]),
                    &ints(&[-rng.range(-9, 9), 1]),
                ),
            )
        }
        // Roots `a/N` and `(a+1)/N` for a large `N`: a cell of width `1/N` that
        // holds no integer and no rational of denominator at most 16, so the
        // `pick` ladder is FORCED past its top two rungs. Added because the
        // ladder's lower rungs were measured unreachable — see `gen_ia`'s note.
        "narrow" => {
            let n = 1_000i64;
            let a = rng.range(-9, 9) * 7;
            (
                pmul(&ints(&[-a, n]), &ints(&[-(a + 1), n])),
                pmul(&ints(&[-(a + 3), n]), &ints(&[-(a + 4), n])),
            )
        }
        _ => {
            let deg = 2 + usize::try_from(rng.below(3)).unwrap_or(0);
            let mut c: Vec<BigInt> = (0..=deg).map(|_| BigInt::from(rng.range(-9, 9))).collect();
            if c[deg].is_zero() {
                c[deg] = BigInt::one();
            }
            let mut c2: Vec<BigInt> = (0..=deg).map(|_| BigInt::from(rng.range(-9, 9))).collect();
            if c2[deg].is_zero() {
                c2[deg] = BigInt::one();
            }
            (
                pmul(&c, &ints(&[-rng.range(-4, 4), 1])),
                pmul(&c2, &ints(&[-rng.range(-4, 4), 1])),
            )
        }
    };
    let cond = match rng.below(6) {
        0 => OISignCond::Lt,
        1 => OISignCond::Le,
        2 => OISignCond::Eq,
        3 => OISignCond::Ne,
        4 => OISignCond::Ge,
        _ => OISignCond::Gt,
    };
    // Probe points: integers, halves and thirds, so both dyadic and
    // non-dyadic rationals are asked about.
    let points: Vec<BigRational> = (0..6)
        .map(|i| {
            let den = if i % 2 == 0 { 1 } else { 3 };
            BigRational::new(BigInt::from(rng.range(-8, 8)), BigInt::from(den))
        })
        .collect();
    GenIA {
        p,
        q,
        cond,
        points,
        strict: rng.next_u64(),
        shape,
    }
}

// ===========================================================================
// Shared plumbing
// ===========================================================================

/// One interval as BOTH sides see it: AY's flattened form, and z3's ASTs for
/// the same two endpoints.
struct Pair {
    ay: OIAlgInterval,
    lo: Option<Ast>,
    hi: Option<Ast>,
}

/// A point to probe, as both sides see it.
struct Probe {
    label: String,
    ay: ODyadicAnum,
    z3: Ast,
}

/// Build AY numbers and z3 ASTs for every real root of `p`, ascending.
fn roots_of(z3: &Z3, p: &[BigInt]) -> Option<Vec<(ODyadicAnum, Ast)>> {
    let rs = z3.roots(&rationals(p))?;
    let mut out = Vec::with_capacity(rs.len());
    for v in rs {
        let iv = dyadic_iv(z3, v)?;
        let a = ODyadicAnum::from_poly_interval(p, &iv)?;
        out.push((a, v));
    }
    if z3.errored() {
        return None;
    }
    Some(out)
}

/// Whether generated intervals include unbounded rays.
#[derive(Clone, Copy)]
enum EndpointExtent {
    Bounded,
    OpenEnded,
}

/// Pair the roots up into intervals `(r0, r1)`, `(r2, r3)`, ... with strictness
/// drawn from `strict`. `base_lit` seeds the justification so each interval is
/// distinguishable.
fn pairs_from(
    roots: &[(ODyadicAnum, Ast)],
    strict: u64,
    base_lit: i32,
    extent: EndpointExtent,
) -> Vec<Pair> {
    let mut out = Vec::new();
    let mut bit = 0u32;
    let take = |b: &mut u32| -> bool {
        let v = (strict >> (*b % 64)) & 1 == 1;
        *b += 1;
        v
    };
    if matches!(extent, EndpointExtent::OpenEnded) && !roots.is_empty() {
        out.push(Pair {
            ay: OIAlgInterval {
                lo: None,
                lo_open: true,
                hi: Some(roots[0].0.clone()),
                hi_open: take(&mut bit),
                lits: vec![base_lit],
            },
            lo: None,
            hi: Some(roots[0].1),
        });
    }
    for (i, w) in roots.chunks(2).enumerate() {
        if w.len() < 2 {
            break;
        }
        out.push(Pair {
            ay: OIAlgInterval {
                lo: Some(w[0].0.clone()),
                lo_open: take(&mut bit),
                hi: Some(w[1].0.clone()),
                hi_open: take(&mut bit),
                lits: vec![base_lit + 1 + i32::try_from(i).unwrap_or(0)],
            },
            lo: Some(w[0].1),
            hi: Some(w[1].1),
        });
    }
    if matches!(extent, EndpointExtent::OpenEnded) && !roots.is_empty() {
        let last = &roots[roots.len() - 1];
        out.push(Pair {
            ay: OIAlgInterval {
                lo: Some(last.0.clone()),
                lo_open: take(&mut bit),
                hi: None,
                hi_open: true,
                lits: vec![base_lit + 40],
            },
            lo: Some(last.1),
            hi: None,
        });
    }
    out
}

/// Membership in the union of the RAW intervals, computed entirely by z3.
///
/// This is the reference answer. It never looks at AY's normalised set, so
/// sorting, merging and empty-dropping are all under test rather than assumed.
fn z3_member(z3: &Z3, pairs: &[Pair], x: Ast) -> Option<bool> {
    for p in pairs {
        let lo_ok = match p.lo {
            None => true,
            Some(l) => {
                if p.ay.lo_open {
                    z3.gt(x, l)?
                } else {
                    z3.gt(x, l)? || z3.eq(x, l)?
                }
            }
        };
        if !lo_ok {
            continue;
        }
        let hi_ok = match p.hi {
            None => true,
            Some(h) => {
                if p.ay.hi_open {
                    z3.lt(x, h)?
                } else {
                    z3.lt(x, h)? || z3.eq(x, h)?
                }
            }
        };
        if hi_ok {
            return Some(true);
        }
    }
    Some(false)
}

/// The probe list: every rational point drawn, PLUS every endpoint as a genuine
/// algebraic number.
///
/// The endpoints are the whole point. A corpus of rational probes cannot tell
/// `(a, b)` from `[a, b]` when `a` is irrational, so every strictness defect
/// would be a question the code cannot get wrong.
fn probes(z3: &Z3, g: &GenIA, roots: &[(ODyadicAnum, Ast)]) -> Option<Vec<Probe>> {
    let mut out = Vec::with_capacity(g.points.len() + roots.len());
    for r in &g.points {
        out.push(Probe {
            label: r.to_string(),
            ay: ODyadicAnum::rational(r.clone()),
            z3: z3.rational(r)?,
        });
    }
    for (i, (a, v)) in roots.iter().enumerate() {
        out.push(Probe {
            label: format!("root{i}"),
            ay: a.clone(),
            z3: *v,
        });
    }
    Some(out)
}

/// The ceilings are asserted BEFORE any consumer runs, so that a later `None`
/// can be reported as a divergence rather than excused as a ceiling decline.
fn under_ceilings(pairs: &[Pair]) -> bool {
    pairs.len() <= oialg_max_intervals()
        && pairs.iter().all(|p| p.ay.lits.len() <= oialg_max_just())
}

fn build(pairs: &[Pair]) -> Option<OIAlgSet> {
    let parts: Vec<OIAlgInterval> = pairs.iter().map(|p| p.ay.clone()).collect();
    OIAlgSet::from_parts(&parts)
}

fn add_matches(total: &mut u64, outcome: Outcome) -> Result<(), Outcome> {
    match outcome {
        Outcome::Match(n) => {
            *total += n;
            Ok(())
        }
        other => Err(other),
    }
}

mod complement;
mod intersect;
mod membership;
mod pick;
mod sign_cells;

pub(crate) use complement::check_complement;
pub(crate) use intersect::check_intersect;
pub(crate) use membership::check_membership;
pub(crate) use pick::check_pick;
pub(crate) use sign_cells::check_sign_cells;
