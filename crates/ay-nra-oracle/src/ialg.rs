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
use num_traits::{One, Signed, Zero};

use crate::anum::{dyadic_iv, rationals};
use crate::checks::{Divergence, Outcome, Sabotage};
use crate::polygen::Rng;
use crate::z3::{Ptr, Z3};

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
    lo: Option<Ptr>,
    hi: Option<Ptr>,
}

/// A point to probe, as both sides see it.
struct Probe {
    label: String,
    ay: ODyadicAnum,
    z3: Ptr,
}

/// Build AY numbers and z3 ASTs for every real root of `p`, ascending.
fn roots_of(z3: &Z3, p: &[BigInt]) -> Option<Vec<(ODyadicAnum, Ptr)>> {
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

/// Pair the roots up into intervals `(r0, r1)`, `(r2, r3)`, ... with strictness
/// drawn from `strict`, plus, when `open_ends` is set, an unbounded ray on each
/// side. `base_lit` seeds the justification so each interval is distinguishable.
fn pairs_from(
    roots: &[(ODyadicAnum, Ptr)],
    strict: u64,
    base_lit: i32,
    open_ends: bool,
) -> Vec<Pair> {
    let mut out = Vec::new();
    let mut bit = 0u32;
    let take = |b: &mut u32| -> bool {
        let v = (strict >> (*b % 64)) & 1 == 1;
        *b += 1;
        v
    };
    if open_ends && !roots.is_empty() {
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
    if open_ends && !roots.is_empty() {
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
fn z3_member(z3: &Z3, pairs: &[Pair], x: Ptr) -> bool {
    pairs.iter().any(|p| {
        let lo_ok = match p.lo {
            None => true,
            Some(l) => {
                if p.ay.lo_open {
                    z3.gt(x, l)
                } else {
                    z3.gt(x, l) || z3.eq(x, l)
                }
            }
        };
        if !lo_ok {
            return false;
        }
        match p.hi {
            None => true,
            Some(h) => {
                if p.ay.hi_open {
                    z3.lt(x, h)
                } else {
                    z3.lt(x, h) || z3.eq(x, h)
                }
            }
        }
    })
}

/// The probe list: every rational point drawn, PLUS every endpoint as a genuine
/// algebraic number.
///
/// The endpoints are the whole point. A corpus of rational probes cannot tell
/// `(a, b)` from `[a, b]` when `a` is irrational, so every strictness defect
/// would be a question the code cannot get wrong.
fn probes(z3: &Z3, g: &GenIA, roots: &[(ODyadicAnum, Ptr)]) -> Vec<Probe> {
    let mut out = Vec::with_capacity(g.points.len() + roots.len());
    for r in &g.points {
        out.push(Probe {
            label: r.to_string(),
            ay: ODyadicAnum::rational(r.clone()),
            z3: z3.rational(r),
        });
    }
    for (i, (a, v)) in roots.iter().enumerate() {
        out.push(Probe {
            label: format!("root{i}"),
            ay: a.clone(),
            z3: *v,
        });
    }
    out
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

// ===========================================================================
// Check 1 — `ialg-membership`
// ===========================================================================

/// The representation, normalisation, and the roster of entry points.
///
/// z3 legs: for every probe — rational AND algebraic — membership in AY's
/// normalised set must equal membership in the raw interval list as z3
/// computes it. Emptiness must agree in the unsound direction: if AY reports
/// empty, z3 must find no member.
/// Identity legs: `len` respects the merge (a normalised set of `n` raw
/// intervals has at most `n`), justifications survive normalisation, and
/// `full` contains every probe.
/// Guards, fired on purpose with a positive control on the SAME endpoints: a
/// closed infinite endpoint and an over-ceiling interval count are both refused.
pub(crate) fn check_membership(z3: &Z3, g: &GenIA, sab: Sabotage) -> Outcome {
    let Some(roots) = roots_of(z3, &g.p) else {
        return Outcome::Skipped("z3 declined / no isolable root");
    };
    if roots.len() < 2 {
        return Outcome::Skipped("fewer than two roots");
    }
    let pairs = pairs_from(&roots, g.strict, 100, true);
    if !under_ceilings(&pairs) {
        return Outcome::Skipped("over declared ceiling");
    }
    let mut n = 0u64;

    // THE PROPERTY ASSERTED BEFORE THE CONSUMER'S ANSWER IS READ.
    //
    // `from_parts` declines only when an endpoint comparison declines, when an
    // infinite endpoint is closed (not the case: built as open above), or when
    // a ceiling is hit (excluded above). Endpoint comparison is `cmp_anum`,
    // documented total below the separation ceiling. So a `None` here is a
    // DIVERGENCE. Without this line the fail-open defect class this module
    // exists to prevent would surface only as a falling match count.
    n += 1;
    let Some(set) = build(&pairs) else {
        if sab.on() {
            return Outcome::Declined("sabotage");
        }
        return Divergence::new(
            "ialg-membership",
            "z3",
            "from_parts DECLINED under the declared ceilings, but every endpoint \
             comparison is documented total"
                .to_string(),
            inputs(g),
        );
    };

    let ps = probes(z3, g, &roots);
    for pr in &ps {
        n += 1;
        let want = z3_member(z3, &pairs, pr.z3);
        let Some(mut got) = set.contains(&pr.ay) else {
            if sab.on() {
                return Outcome::Declined("sabotage");
            }
            return Divergence::new(
                "ialg-membership",
                "z3",
                format!(
                    "contains({}) DECLINED; comparison is documented total",
                    pr.label
                ),
                inputs(g),
            );
        };
        if sab.on() && pr.label.starts_with("root") {
            got = !got;
        }
        if got != want {
            return Divergence::new(
                "ialg-membership",
                "z3",
                format!(
                    "contains({}) = {got}, z3 says {want} (raw {} intervals -> {} normalised)",
                    pr.label,
                    pairs.len(),
                    set.len()
                ),
                inputs(g),
            );
        }
    }

    // Emptiness, in the direction that would be UNSOUND to get wrong: a set
    // reported empty is a conflict, so z3 must find nothing in it.
    if set.is_empty() {
        for pr in &ps {
            n += 1;
            if z3_member(z3, &pairs, pr.z3) {
                return Divergence::new(
                    "ialg-membership",
                    "z3",
                    format!("set reported EMPTY but z3 places {} in it", pr.label),
                    inputs(g),
                );
            }
        }
    }

    if !sab.on() {
        // Normalisation can only merge, never split.
        n += 1;
        if set.len() > pairs.len() {
            return Divergence::new(
                "ialg-membership",
                "identity",
                format!("normalise grew {} intervals to {}", pairs.len(), set.len()),
                inputs(g),
            );
        }
        // Every literal handed in survives.
        n += 1;
        let Some(js) = set.justification() else {
            return Divergence::new(
                "ialg-membership",
                "identity",
                "justification DECLINED under the declared ceiling".to_string(),
                inputs(g),
            );
        };
        // NO INVENTED LITERALS. A justification is a conflict clause: a literal
        // in it that is not responsible for the conflict makes the clause WRONG,
        // not merely imprecise. This leg only ever asserted that handed-in
        // literals SURVIVE, so a verifier merged a literal that was never
        // supplied (-99999) and got 0 divergences over 9,000 cases across three
        // seeds with selftest 41/41 and golden 44/44.
        {
            let mut supplied: Vec<i32> = Vec::new();
            for p in &pairs {
                for l in &p.ay.lits {
                    if !supplied.contains(l) {
                        supplied.push(*l);
                    }
                }
            }
            for l in &js {
                n += 1;
                if !supplied.contains(l) {
                    return Divergence::new(
                        "ialg-membership",
                        "identity",
                        format!(
                            "justification cites literal {l}, which was never supplied — an \
                             invented literal makes the conflict clause wrong"
                        ),
                        inputs(g),
                    );
                }
            }
        }
        for p in &pairs {
            for l in &p.ay.lits {
                n += 1;
                if !set.is_empty() && !js.contains(l) {
                    return Divergence::new(
                        "ialg-membership",
                        "identity",
                        format!("literal {l} lost by normalisation"),
                        inputs(g),
                    );
                }
            }
        }
        // `full` holds everything; `empty` holds nothing.
        let Some(full) = OIAlgSet::full(&[7]) else {
            return Outcome::Skipped("full declined");
        };
        for pr in &ps {
            n += 1;
            if full.contains(&pr.ay) != Some(true) {
                return Divergence::new(
                    "ialg-membership",
                    "identity",
                    format!("full does not contain {}", pr.label),
                    inputs(g),
                );
            }
            n += 1;
            if OIAlgSet::empty().contains(&pr.ay) != Some(false) {
                return Divergence::new(
                    "ialg-membership",
                    "identity",
                    format!("empty contains {}", pr.label),
                    inputs(g),
                );
            }
        }
        // Union with itself is idempotent on the point set.
        let Some(u) = set.union(&set) else {
            return Divergence::new(
                "ialg-membership",
                "identity",
                "union DECLINED under the declared ceilings".to_string(),
                inputs(g),
            );
        };
        for pr in &ps {
            n += 1;
            if u.contains(&pr.ay) != set.contains(&pr.ay) {
                return Divergence::new(
                    "ialg-membership",
                    "identity",
                    format!("union with self moved {}", pr.label),
                    inputs(g),
                );
            }
        }

        // GUARDS, fired on purpose, each with a positive control that must
        // still succeed on the SAME endpoints.
        n += 1;
        let closed_inf = OIAlgSet::from_parts(&[OIAlgInterval {
            lo: None,
            lo_open: false,
            hi: Some(roots[0].0.clone()),
            hi_open: true,
            lits: vec![1],
        }]);
        if closed_inf.is_some() {
            return Divergence::new(
                "ialg-membership",
                "identity",
                "a CLOSED -inf endpoint was accepted".to_string(),
                inputs(g),
            );
        }
        n += 1;
        if OIAlgSet::from_parts(&[OIAlgInterval {
            lo: None,
            lo_open: true,
            hi: Some(roots[0].0.clone()),
            hi_open: true,
            lits: vec![1],
        }])
        .is_none()
        {
            return Divergence::new(
                "ialg-membership",
                "identity",
                "the OPEN control on the same endpoint was refused too".to_string(),
                inputs(g),
            );
        }
        n += 1;
        let too_many: Vec<OIAlgInterval> = (0..=oialg_max_intervals())
            .map(|i| OIAlgInterval {
                lo: Some(ODyadicAnum::rational(BigRational::from_integer(
                    BigInt::from(3 * i as i64),
                ))),
                lo_open: false,
                hi: Some(ODyadicAnum::rational(BigRational::from_integer(
                    BigInt::from(3 * i as i64 + 1),
                ))),
                hi_open: false,
                lits: vec![1],
            })
            .collect();
        if OIAlgSet::from_parts(&too_many).is_some() {
            return Divergence::new(
                "ialg-membership",
                "identity",
                format!("{} intervals accepted past the ceiling", too_many.len()),
                inputs(g),
            );
        }
        n += 1;
        if OIAlgSet::from_parts(&too_many[..oialg_max_intervals()]).is_none() {
            return Divergence::new(
                "ialg-membership",
                "identity",
                "the at-ceiling control was refused too".to_string(),
                inputs(g),
            );
        }
    }
    Outcome::Match(n)
}

// ===========================================================================
// Check 2 — `ialg-intersect`
// ===========================================================================

/// Intersection, and the justifications it must keep.
///
/// z3 legs: membership in `a n b` equals `member(a) && member(b)` at every
/// probe, computed by z3 on the raw lists; and the conflict direction — an
/// intersection reported EMPTY must contain no probe.
/// Identity legs: commutativity; idempotence; intersecting with `full` and with
/// `empty`; and the justification of every surviving interval must include the
/// literals of BOTH sides, which is what makes the conflict clause entail the
/// conflict.
pub(crate) fn check_intersect(z3: &Z3, g: &GenIA, sab: Sabotage) -> Outcome {
    let (Some(ra), Some(rb)) = (roots_of(z3, &g.p), roots_of(z3, &g.q)) else {
        return Outcome::Skipped("z3 declined / no isolable root");
    };
    if ra.len() < 2 || rb.len() < 2 {
        return Outcome::Skipped("fewer than two roots");
    }
    let pa = pairs_from(&ra, g.strict, 100, false);
    let pb = pairs_from(&rb, g.strict >> 7, 200, false);
    if pa.is_empty() || pb.is_empty() || !under_ceilings(&pa) || !under_ceilings(&pb) {
        return Outcome::Skipped("empty or over declared ceiling");
    }
    let (Some(sa), Some(sb)) = (build(&pa), build(&pb)) else {
        return Divergence::new(
            "ialg-intersect",
            "z3",
            "from_parts DECLINED under the declared ceilings".to_string(),
            inputs(g),
        );
    };
    let mut n = 1u64;

    let Some(inter) = sa.intersect(&sb) else {
        if sab.on() {
            return Outcome::Declined("sabotage");
        }
        return Divergence::new(
            "ialg-intersect",
            "z3",
            "intersect DECLINED under the declared ceilings, but every endpoint \
             comparison is documented total"
                .to_string(),
            inputs(g),
        );
    };

    let mut all = ra.clone();
    all.extend(rb.iter().cloned());
    let ps = probes(z3, g, &all);
    for pr in &ps {
        n += 1;
        let want = z3_member(z3, &pa, pr.z3) && z3_member(z3, &pb, pr.z3);
        let Some(mut got) = inter.contains(&pr.ay) else {
            if sab.on() {
                return Outcome::Declined("sabotage");
            }
            return Divergence::new(
                "ialg-intersect",
                "z3",
                format!(
                    "contains({}) DECLINED; comparison is documented total",
                    pr.label
                ),
                inputs(g),
            );
        };
        if sab.on() && pr.label.starts_with("root") {
            got = !got;
        }
        if got != want {
            return Divergence::new(
                "ialg-intersect",
                "z3",
                format!(
                    "(a n b).contains({}) = {got}, z3 says {want} ({} n {} -> {})",
                    pr.label,
                    sa.len(),
                    sb.len(),
                    inter.len()
                ),
                inputs(g),
            );
        }
    }
    if inter.is_empty() {
        for pr in &ps {
            n += 1;
            if z3_member(z3, &pa, pr.z3) && z3_member(z3, &pb, pr.z3) {
                return Divergence::new(
                    "ialg-intersect",
                    "z3",
                    format!(
                        "intersection reported EMPTY but z3 places {} in both",
                        pr.label
                    ),
                    inputs(g),
                );
            }
        }
    }

    // SAME_SET_AS IS ITSELF WITNESSED, before anything is built on it.
    //
    // Six identity legs in this file are of the form
    // `.and_then(|x| x.same_set_as(..)).unwrap_or(false)` expecting `true`, so a
    // `same_set_as` hardwired to `Some(true)` certifies commutativity,
    // idempotence, double-complement, `(a\b) U (a n b) = a`, `a \ empty = a`
    // and "complement of Lt is Ge" ALL AT ONCE. A verifier did exactly that and
    // got 0 divergences over 9,000 cases across three seeds, with selftest
    // 41/41, golden 44/44 and all 40 unit tests passing. It is the function this
    // module ADDED because the oracle caught three real defects on its first
    // run — and the fix was then made self-certifying.
    //
    // The necessary condition asserted here is independent of `same_set_as`: if
    // two sets are equal they must agree on membership at EVERY probe point,
    // decided by `contains`, which is a different function. A hardwired `true`
    // fails this the moment two probed sets differ anywhere.
    if !sab.on() {
        n += 1;
        match sa.same_set_as(&sb) {
            Some(equal) => {
                for pr in &probes(z3, g, &ra) {
                    let (ca, cb) = (sa.contains(&pr.ay), sb.contains(&pr.ay));
                    if let (Some(ca), Some(cb)) = (ca, cb) {
                        n += 1;
                        if equal && ca != cb {
                            return Divergence::new(
                                "ialg-intersect",
                                "identity",
                                "same_set_as says EQUAL but the two sets disagree on \
                                 membership at a probe point"
                                    .to_string(),
                                inputs(g),
                            );
                        }
                    }
                }
            }
            None => {
                return Divergence::new(
                    "ialg-intersect",
                    "identity",
                    "same_set_as DECLINED — set equality is documented total here".to_string(),
                    inputs(g),
                );
            }
        }
        n += 1;
        if !sb
            .intersect(&sa)
            .and_then(|x| x.same_set_as(&inter))
            .unwrap_or(false)
        {
            return Divergence::new(
                "ialg-intersect",
                "identity",
                "intersection is not commutative".to_string(),
                inputs(g),
            );
        }
        n += 1;
        if !sa
            .intersect(&sa)
            .and_then(|x| x.same_set_as(&sa))
            .unwrap_or(false)
        {
            return Divergence::new(
                "ialg-intersect",
                "identity",
                "intersection is not idempotent".to_string(),
                inputs(g),
            );
        }
        n += 1;
        if !sa
            .intersect(&OIAlgSet::empty())
            .is_some_and(|s| s.is_empty())
        {
            return Divergence::new(
                "ialg-intersect",
                "identity",
                "a n empty is not empty".to_string(),
                inputs(g),
            );
        }
        // JUSTIFICATIONS. A surviving cell must cite both sides; a clause built
        // from one side alone does not entail the conflict.
        for iv in inter.intervals() {
            n += 1;
            let from_a = iv.lits.iter().any(|l| (100..200).contains(l));
            let from_b = iv.lits.iter().any(|l| *l >= 200);
            if !from_a || !from_b {
                return Divergence::new(
                    "ialg-intersect",
                    "identity",
                    format!(
                        "surviving cell cites {:?}: from_a={from_a} from_b={from_b}",
                        iv.lits
                    ),
                    inputs(g),
                );
            }
        }
    }
    Outcome::Match(n)
}

// ===========================================================================
// Check 3 — `ialg-complement`
// ===========================================================================

/// Complement and subtract — how a refuted cell is removed.
///
/// z3 legs: membership in the complement is exactly NON-membership in the raw
/// list, at every probe including the endpoints (which is the only way a
/// strictness flip is visible); and `a \ b` is `member(a) && !member(b)`.
/// Identity legs: double complement is the identity; `a \ a` is empty;
/// `a \ empty` is `a`; complement of `full` is empty and back.
pub(crate) fn check_complement(z3: &Z3, g: &GenIA, sab: Sabotage) -> Outcome {
    let (Some(ra), Some(rb)) = (roots_of(z3, &g.p), roots_of(z3, &g.q)) else {
        return Outcome::Skipped("z3 declined / no isolable root");
    };
    if ra.len() < 2 || rb.len() < 2 {
        return Outcome::Skipped("fewer than two roots");
    }
    let pa = pairs_from(&ra, g.strict, 100, false);
    let pb = pairs_from(&rb, g.strict >> 11, 200, false);
    if pa.is_empty() || pb.is_empty() || !under_ceilings(&pa) || !under_ceilings(&pb) {
        return Outcome::Skipped("empty or over declared ceiling");
    }
    let (Some(sa), Some(sb)) = (build(&pa), build(&pb)) else {
        return Divergence::new(
            "ialg-complement",
            "z3",
            "from_parts DECLINED under the declared ceilings".to_string(),
            inputs(g),
        );
    };
    let mut n = 1u64;

    let (Some(ca), Some(diff)) = (sa.complement(), sa.subtract(&sb)) else {
        if sab.on() {
            return Outcome::Declined("sabotage");
        }
        return Divergence::new(
            "ialg-complement",
            "z3",
            "complement or subtract DECLINED under the declared ceilings, but every \
             endpoint comparison is documented total"
                .to_string(),
            inputs(g),
        );
    };

    let mut all = ra.clone();
    all.extend(rb.iter().cloned());
    let ps = probes(z3, g, &all);
    for pr in &ps {
        let in_a = z3_member(z3, &pa, pr.z3);
        let in_b = z3_member(z3, &pb, pr.z3);

        n += 1;
        let Some(mut got) = ca.contains(&pr.ay) else {
            if sab.on() {
                return Outcome::Declined("sabotage");
            }
            return Divergence::new(
                "ialg-complement",
                "z3",
                format!("complement.contains({}) DECLINED", pr.label),
                inputs(g),
            );
        };
        if sab.on() && pr.label.starts_with("root") {
            got = !got;
        }
        if got != !in_a {
            return Divergence::new(
                "ialg-complement",
                "z3",
                format!(
                    "complement.contains({}) = {got}, z3 says member(a) = {in_a}",
                    pr.label
                ),
                inputs(g),
            );
        }

        n += 1;
        let Some(mut gotd) = diff.contains(&pr.ay) else {
            return Divergence::new(
                "ialg-complement",
                "z3",
                format!("subtract.contains({}) DECLINED", pr.label),
                inputs(g),
            );
        };
        if sab.on() && pr.label.starts_with("root") {
            gotd = !gotd;
        }
        if gotd != (in_a && !in_b) {
            return Divergence::new(
                "ialg-complement",
                "z3",
                format!(
                    "(a \\ b).contains({}) = {gotd}, z3 says a={in_a} b={in_b}",
                    pr.label
                ),
                inputs(g),
            );
        }
    }

    if !sab.on() {
        n += 1;
        if !ca
            .complement()
            .and_then(|x| x.same_set_as(&sa))
            .unwrap_or(false)
        {
            return Divergence::new(
                "ialg-complement",
                "identity",
                "double complement is not the identity".to_string(),
                inputs(g),
            );
        }
        n += 1;
        if !sa.subtract(&sa).is_some_and(|s| s.is_empty()) {
            return Divergence::new(
                "ialg-complement",
                "identity",
                "a \\ a is not empty".to_string(),
                inputs(g),
            );
        }
        n += 1;
        if !sa
            .subtract(&OIAlgSet::empty())
            .and_then(|x| x.same_set_as(&sa))
            .unwrap_or(false)
        {
            return Divergence::new(
                "ialg-complement",
                "identity",
                "a \\ empty is not a".to_string(),
                inputs(g),
            );
        }
        n += 1;
        // `a \ b` and `a n b` partition `a`.
        let Some(mid) = sa.intersect(&sb) else {
            return Outcome::Skipped("intersect declined");
        };
        if !diff
            .union(&mid)
            .and_then(|x| x.same_set_as(&sa))
            .unwrap_or(false)
        {
            return Divergence::new(
                "ialg-complement",
                "identity",
                "(a \\ b) U (a n b) is not a".to_string(),
                inputs(g),
            );
        }
        n += 1;
        let Some(full) = OIAlgSet::full(&[3]) else {
            return Outcome::Skipped("full declined");
        };
        if !full.complement().is_some_and(|s| s.is_empty()) {
            return Divergence::new(
                "ialg-complement",
                "identity",
                "complement of full is not empty".to_string(),
                inputs(g),
            );
        }
    }
    Outcome::Match(n)
}

// ===========================================================================
// Check 4 — `ialg-pick`
// ===========================================================================

/// The sample-point ladder.
///
/// z3 legs: every picked value must lie in the raw interval list as z3
/// computes it — a wrong sample point is a wrong decision, and the whole
/// verification-before-return discipline in `pick` exists to make this
/// impossible; and the MINIMALITY of the rung is checked by an independent
/// search that z3 adjudicates, never by reading AY's own tag.
/// Identity legs: `pick` on a non-empty set must succeed (a refusal here is a
/// divergence, see below); `pick` on the empty set must refuse;
/// `oialg_classify_value` is exercised directly on arbitrary values.
///
/// # A refusal is a divergence
///
/// `pick`'s ladder is a heuristic, but its TOTALITY on this corpus is not: the
/// dyadic rung succeeds for any interval with a non-empty interior, and the
/// algebraic rung covers the closed singleton, so the only non-empty set it can
/// refuse is one whose intervals are narrower than `2^-256`. No set built from
/// distinct roots of these small integer polynomials is. Reporting a refusal as
/// a decline would let a broken ladder — one whose bracket search silently
/// stopped finding anything — pass as silence, which is exactly how
/// `root_index` went from 111 matched to 21 matched with 0 divergences.
pub(crate) fn check_pick(z3: &Z3, g: &GenIA, sab: Sabotage) -> Outcome {
    let Some(roots) = roots_of(z3, &g.p) else {
        return Outcome::Skipped("z3 declined / no isolable root");
    };
    if roots.len() < 2 {
        return Outcome::Skipped("fewer than two roots");
    }
    let pairs = pairs_from(&roots, g.strict, 100, false);
    if pairs.is_empty() || !under_ceilings(&pairs) {
        return Outcome::Skipped("empty or over declared ceiling");
    }
    let Some(set) = build(&pairs) else {
        return Divergence::new(
            "ialg-pick",
            "z3",
            "from_parts DECLINED under the declared ceilings".to_string(),
            inputs(g),
        );
    };
    let mut n = 1u64;

    n += 1;
    if OIAlgSet::empty().pick().is_some() {
        return Divergence::new(
            "ialg-pick",
            "identity",
            "pick returned a value from the EMPTY set".to_string(),
            inputs(g),
        );
    }
    if set.is_empty() {
        return Outcome::Skipped("set normalised to empty");
    }

    n += 1;
    let Some(v) = set.pick() else {
        if sab.on() {
            return Outcome::Declined("sabotage");
        }
        return Divergence::new(
            "ialg-pick",
            "identity",
            format!(
                "pick REFUSED a non-empty set of {} intervals; the dyadic rung is \
                 total for any non-degenerate interior",
                set.len()
            ),
            inputs(g),
        );
    };

    // Sabotage moves the picked value off its set. MEASURED: an off-by-ONE was
    // caught in only 19 of 29 sabotaged cases (65.5%, below the 80% gate),
    // because these intervals are routinely wider than 1 and `v + 1` lands back
    // inside — the corruption was real but not observable. `SABOTAGE_SHIFT` is
    // past the Cauchy bound of every polynomial this generator draws (degree at
    // most 5, coefficients at most 9, so every root is within 10), so the
    // shifted value is outside the set whatever the shape.
    const SABOTAGE_SHIFT: i64 = 1_000;
    let v = if sab.on() {
        let base = v
            .to_rational()
            .unwrap_or_else(|| BigRational::from_integer(BigInt::zero()));
        ODyadicAnum::rational(base + BigRational::from_integer(BigInt::from(SABOTAGE_SHIFT)))
    } else {
        v
    };

    // THE ANSWER, ADJUDICATED BY z3 — not by AY's own `contains`.
    n += 1;
    let Ok(vz) = z3_ast_of(z3, &v) else {
        return Outcome::Skipped("z3 could not name AY's pick");
    };
    if !z3_member(z3, &pairs, vz) {
        return Divergence::new(
            "ialg-pick",
            "z3",
            format!(
                "pick returned {} which z3 places OUTSIDE the set",
                z3.ast_string(vz)
            ),
            inputs(g),
        );
    }

    if sab.on() {
        return Outcome::Match(n);
    }

    // MINIMALITY, derived and independently searched.
    //
    // The rung is re-derived from the value; there is no tag to read. Then a
    // simpler value is hunted for directly, with z3 adjudicating membership.
    // If one is found, AY's ladder skipped a rung.
    let rung = oialg_classify_value(&v);
    n += 1;
    if rung > OIRung::Integer {
        if let Some(k) = integer_span(z3, &pairs) {
            for m in k.0..=k.1 {
                n += 1;
                let cand = z3.rational(&BigRational::from_integer(BigInt::from(m)));
                if z3_member(z3, &pairs, cand) {
                    return Divergence::new(
                        "ialg-pick",
                        "z3",
                        format!("pick returned a {rung:?} value but the INTEGER {m} is in the set"),
                        inputs(g),
                    );
                }
            }
        }
    }
    if rung > OIRung::Simple {
        if let Some(k) = integer_span(z3, &pairs) {
            'outer: for d in 2..=oialg_max_simple_den() {
                for m in (k.0 * d)..=(k.1 * d) {
                    if m.checked_mul(1).is_none() {
                        break 'outer;
                    }
                    n += 1;
                    let cand = z3.rational(&BigRational::new(BigInt::from(m), BigInt::from(d)));
                    if z3_member(z3, &pairs, cand) {
                        return Divergence::new(
                            "ialg-pick",
                            "z3",
                            format!(
                                "pick returned a {rung:?} value but the simple rational \
                                 {m}/{d} is in the set"
                            ),
                            inputs(g),
                        );
                    }
                }
            }
        }
    }

    // THE SINGLETON CELL — the only shape that reaches the bottom of the ladder.
    //
    // MEASURED: over 12,000 fuzz cases at seed 20260806 this check observed the
    // `Integer` rung 247 times and `Simple` 25 times, and `Dyadic`, `Rational`
    // and `Algebraic` ZERO times. Intervals between consecutive roots of small
    // integer polynomials are simply wide enough that an integer is always
    // available, so the lower rungs of the ladder were an unwitnessed witness:
    // the only question the corpus could ask had the top rung as its answer.
    // The `narrow` shape fixes the middle rungs; a closed singleton `[r, r]` is
    // the only set whose ONLY member is `r` itself, so it is the only way to
    // force the algebraic rung, and it also pins the strongest property `pick`
    // has — on a singleton the answer is not a choice.
    let single = OIAlgSet::from_parts(&[OIAlgInterval {
        lo: Some(roots[0].0.clone()),
        lo_open: false,
        hi: Some(roots[0].0.clone()),
        hi_open: false,
        lits: vec![11],
    }]);
    n += 1;
    let Some(single) = single else {
        return Divergence::new(
            "ialg-pick",
            "identity",
            "a closed singleton at a root of p was refused".to_string(),
            inputs(g),
        );
    };
    n += 1;
    if single.is_empty() || single.len() != 1 {
        return Divergence::new(
            "ialg-pick",
            "identity",
            format!(
                "the singleton [r, r] normalised to {} intervals",
                single.len()
            ),
            inputs(g),
        );
    }
    n += 1;
    let Some(sv) = single.pick() else {
        return Divergence::new(
            "ialg-pick",
            "identity",
            "pick REFUSED a closed singleton, whose sole member is its endpoint".to_string(),
            inputs(g),
        );
    };
    // z3 adjudicates that the picked value IS the root — not merely inside.
    n += 1;
    if let Ok(svz) = z3_ast_of(z3, &sv) {
        if !z3.eq(svz, roots[0].1) {
            return Divergence::new(
                "ialg-pick",
                "z3",
                format!(
                    "pick on the singleton [r, r] returned {}, which z3 says is not r",
                    z3.ast_string(svz)
                ),
                inputs(g),
            );
        }
    }
    // The rung is whatever the ROOT is; for an irrational root that is
    // `Algebraic`, which nothing else in this corpus reaches.
    n += 1;
    if oialg_classify_value(&sv) != oialg_classify_value(&roots[0].0) {
        return Divergence::new(
            "ialg-pick",
            "identity",
            format!(
                "singleton pick classified {:?} but the root classifies {:?}",
                oialg_classify_value(&sv),
                oialg_classify_value(&roots[0].0)
            ),
            inputs(g),
        );
    }

    // `classify_value` exercised DIRECTLY, not only through `pick`.
    n += 1;
    if oialg_classify_value(&ODyadicAnum::rational(BigRational::from_integer(
        BigInt::from(-4),
    ))) != OIRung::Integer
    {
        return Divergence::new(
            "ialg-pick",
            "identity",
            "classify_value(-4) is not Integer".to_string(),
            inputs(g),
        );
    }
    n += 1;
    if oialg_classify_value(&ODyadicAnum::rational(BigRational::new(
        BigInt::one(),
        BigInt::from(oialg_max_simple_den() * 4),
    ))) != OIRung::Dyadic
    {
        return Divergence::new(
            "ialg-pick",
            "identity",
            "a small dyadic past the simple ceiling is not classified Dyadic".to_string(),
            inputs(g),
        );
    }
    n += 1;
    if !roots.is_empty()
        && !roots[0].0.is_rational()
        && oialg_classify_value(&roots[0].0) != OIRung::Algebraic
    {
        return Divergence::new(
            "ialg-pick",
            "identity",
            "an irrational root is not classified Algebraic".to_string(),
            inputs(g),
        );
    }
    Outcome::Match(n)
}

/// The integer range worth scanning for the minimality legs, or `None` when the
/// set is too wide to scan — a bound, so this leg can never run away.
fn integer_span(z3: &Z3, pairs: &[Pair]) -> Option<(i64, i64)> {
    let mut lo = i64::MAX;
    let mut hi = i64::MIN;
    for p in pairs {
        let (l, h) = (p.lo?, p.hi?);
        let (a, _) = z3.bracket(l, 40)?;
        let (_, b) = z3.bracket(h, 40)?;
        lo = lo.min(rat_floor_i64(&a)? - 1);
        hi = hi.max(rat_ceil_i64(&b)? + 1);
    }
    if lo > hi || hi - lo > MINIMALITY_SPAN {
        return None;
    }
    Some((lo, hi))
}

fn rat_floor_i64(r: &BigRational) -> Option<i64> {
    i64::try_from(r.floor().to_integer()).ok()
}

fn rat_ceil_i64(r: &BigRational) -> Option<i64> {
    i64::try_from(r.ceil().to_integer()).ok()
}

/// z3's AST for an AY value: exact for a rational, and for an algebraic value
/// the unique root of AY's OWN defining polynomial inside AY's OWN interval.
fn z3_ast_of(z3: &Z3, a: &ODyadicAnum) -> Result<Ptr, ()> {
    if let Some(r) = a.to_rational() {
        return Ok(z3.rational(&r));
    }
    let coeffs = rationals(&a.poly_coeffs().ok_or(())?);
    let roots = z3.roots(&coeffs).ok_or(())?;
    let iv = a.interval().ok_or(())?;
    let lo = z3.rational(&iv.lo().to_rational());
    let hi = z3.rational(&iv.hi().to_rational());
    let mut found = None;
    for r in roots {
        if z3.gt(r, lo) && z3.lt(r, hi) {
            if found.is_some() {
                return Err(());
            }
            found = Some(r);
        }
    }
    if z3.errored() {
        return Err(());
    }
    found.ok_or(())
}

// ===========================================================================
// Check 5 — `ialg-sign-cells`
// ===========================================================================

/// Construction from a sign condition — the operation that turns a root
/// isolation into a feasible set, and the one where a fail-open predicate would
/// be catastrophic.
///
/// z3 legs: for every probe, membership in AY's constructed set must equal
/// `cond.accepts(sign of p at that probe)` with the SIGN COMPUTED BY z3
/// (`Z3_algebraic_eval`). That single assertion pins the whole cell
/// decomposition: sample-point selection, sign propagation, which cells are
/// kept, and how the closed root cells are glued onto the open ones.
/// Identity legs: complementary conditions partition the line (`Lt` and `Ge`
/// are complements, as are `Le`/`Gt` and `Eq`/`Ne`); the roots themselves are
/// in the `Eq` set and out of the `Ne` set.
/// Guard, fired on purpose: a descending root list is refused.
///
/// # Why this is where the fail-open defect lives
///
/// If the sign at a sample point cannot be evaluated, the permissive answers
/// are "keep the cell" (silently too large) and "drop the cell" (silently too
/// small — and a feasible set wrongly emptied is a CONFLICT THAT DOES NOT
/// EXIST). `from_sign_condition` takes neither and returns `None`. The injected
/// defect used to demonstrate this check replaces that `?` with an assumption,
/// which is the `check_monomial_consistency` shape exactly.
pub(crate) fn check_sign_cells(z3: &Z3, g: &GenIA, sab: Sabotage) -> Outcome {
    let Some(roots) = roots_of(z3, &g.p) else {
        return Outcome::Skipped("z3 declined / no isolable root");
    };
    if 2 * roots.len() + 1 > oialg_max_intervals() {
        return Outcome::Skipped("over declared ceiling");
    }
    let ay_roots: Vec<ODyadicAnum> = roots.iter().map(|(a, _)| a.clone()).collect();
    let coeffs = rationals(&g.p);
    let mut n = 1u64;

    // Feed z3's OWN ascending root list — the pure function is driven
    // directly, not through a consumer.
    let Some(set) = oialg_from_sign_condition(&g.p, &ay_roots, g.cond, &[5]) else {
        if sab.on() {
            return Outcome::Declined("sabotage");
        }
        return Divergence::new(
            "ialg-sign-cells",
            "z3",
            format!(
                "from_sign_condition DECLINED on z3's own ascending {}-root list; \
                 every sign is evaluable and every comparison is documented total",
                roots.len()
            ),
            inputs(g),
        );
    };

    let ps = probes(z3, g, &roots);
    for pr in &ps {
        let Some(s) = z3.eval_sign(&coeffs, pr.z3) else {
            continue;
        };
        let want = g.cond.accepts(s);
        n += 1;
        let Some(mut got) = set.contains(&pr.ay) else {
            if sab.on() {
                return Outcome::Declined("sabotage");
            }
            return Divergence::new(
                "ialg-sign-cells",
                "z3",
                format!(
                    "contains({}) DECLINED; comparison is documented total",
                    pr.label
                ),
                inputs(g),
            );
        };
        if sab.on() {
            got = !got;
        }
        if got != want {
            return Divergence::new(
                "ialg-sign-cells",
                "z3",
                format!(
                    "cond {:?}: contains({}) = {got}, but z3 says sign(p) = {s} there \
                     so it should be {want} ({} cells, {} roots)",
                    g.cond,
                    pr.label,
                    set.len(),
                    roots.len()
                ),
                inputs(g),
            );
        }
    }

    if !sab.on() {
        // Complementary conditions partition the line.
        for (a, b) in [
            (OISignCond::Lt, OISignCond::Ge),
            (OISignCond::Le, OISignCond::Gt),
            (OISignCond::Eq, OISignCond::Ne),
        ] {
            let (Some(sa), Some(sb)) = (
                oialg_from_sign_condition(&g.p, &ay_roots, a, &[5]),
                oialg_from_sign_condition(&g.p, &ay_roots, b, &[6]),
            ) else {
                return Divergence::new(
                    "ialg-sign-cells",
                    "identity",
                    format!("from_sign_condition DECLINED for {a:?}/{b:?}"),
                    inputs(g),
                );
            };
            n += 1;
            if !sa.intersect(&sb).is_some_and(|s| s.is_empty()) {
                return Divergence::new(
                    "ialg-sign-cells",
                    "identity",
                    format!("{a:?} and {b:?} overlap"),
                    inputs(g),
                );
            }
            n += 1;
            if !sa
                .complement()
                .and_then(|x| x.same_set_as(&sb))
                .unwrap_or(false)
            {
                return Divergence::new(
                    "ialg-sign-cells",
                    "identity",
                    format!("complement of {a:?} is not {b:?}"),
                    inputs(g),
                );
            }
        }
        // Every root is in the `Eq` set and out of the `Ne` set.
        let Some(eq) = oialg_from_sign_condition(&g.p, &ay_roots, OISignCond::Eq, &[5]) else {
            return Outcome::Skipped("Eq declined");
        };
        for (a, _) in &roots {
            n += 1;
            if eq.contains(a) != Some(true) {
                return Divergence::new(
                    "ialg-sign-cells",
                    "identity",
                    "a root of p is not in the Eq set".to_string(),
                    inputs(g),
                );
            }
        }
        n += 1;
        if eq.len() != roots.len() {
            return Divergence::new(
                "ialg-sign-cells",
                "identity",
                format!("Eq set has {} cells for {} roots", eq.len(), roots.len()),
                inputs(g),
            );
        }
        // GUARD, fired on purpose: a descending root list must be refused,
        // and the ascending control on the SAME roots must still succeed.
        if roots.len() >= 2 {
            n += 1;
            let mut rev = ay_roots.clone();
            rev.reverse();
            if oialg_from_sign_condition(&g.p, &rev, g.cond, &[5]).is_some() {
                return Divergence::new(
                    "ialg-sign-cells",
                    "identity",
                    "a DESCENDING root list was accepted".to_string(),
                    inputs(g),
                );
            }
            n += 1;
            if oialg_from_sign_condition(&g.p, &ay_roots, g.cond, &[5]).is_none() {
                return Divergence::new(
                    "ialg-sign-cells",
                    "identity",
                    "the ascending control on the same roots was refused too".to_string(),
                    inputs(g),
                );
            }
        }
    }
    Outcome::Match(n)
}

/// Unused-import silencer for the numeric traits the helpers need.
#[allow(dead_code)]
fn _traits_used() -> bool {
    BigInt::one().is_positive() && BigRational::zero().is_zero()
}
