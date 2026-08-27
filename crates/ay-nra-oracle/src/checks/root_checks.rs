// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Included by the parent module to keep one audited namespace.

/// `x - 1/2`: the factor sabotage multiplies into a polynomial answer.
///
/// Its root `1/2` is small enough to fall inside the fuzzer's usual sampling
/// window and is rarely a root of a randomly generated polynomial, so the
/// injected extra root is almost always observable. Measured catch rate under
/// `selftest`: 213/219 for `square-free` — the misses are inputs that already
/// had `1/2` as a root, where multiplying it in again changes nothing z3 can
/// see (it reports DISTINCT roots).
fn saboteur_factor() -> OPoly {
    OPoly::from_coeffs(vec![
        BigRational::new(BigInt::from(-1), BigInt::from(2)),
        BigRational::one(),
    ])
}

/// Maximum polynomial degree the fuzzer generates.
///
/// Measured at this cap, together with the work budget: median case well under
/// a millisecond, ~260 cases/s overall, worst case 6.1 s over a 50 000-case
/// shard. Degree is the dominant cost term because AY's Sturm sequence is a
/// plain Euclidean remainder chain over `Q` with no primitive-part reduction,
/// so its intermediate coefficients grow multiplicatively; raising this cap
/// makes the run measure bignum throughput rather than agreement.
pub(crate) const MAX_DEGREE: usize = 8;

fn poly_of(g: &GenPoly) -> OPoly {
    OPoly::from_coeffs(g.coeffs.clone())
}

fn inputs1(a: &GenPoly) -> Vec<(String, String)> {
    vec![
        ("p".to_string(), polygen::render(&a.coeffs)),
        ("p.shape".to_string(), a.shape.name().to_string()),
    ]
}

fn inputs2(a: &GenPoly, b: &GenPoly) -> Vec<(String, String)> {
    vec![
        ("p".to_string(), polygen::render(&a.coeffs)),
        ("p.shape".to_string(), a.shape.name().to_string()),
        ("q".to_string(), polygen::render(&b.coeffs)),
        ("q.shape".to_string(), b.shape.name().to_string()),
    ]
}

/// Does AY's marker localize the z3 root `r`?
///
/// A `Rational(q)` marker must be *exactly* z3's root; an `Interval(lo, hi)`
/// marker must strictly contain it. There is no tolerance anywhere: both sides
/// are exact, so a near miss is a miss.
fn marker_matches(z3: &Z3, marker: &ORoot, r: Ast) -> Option<bool> {
    match marker {
        ORoot::Rational(q) => {
            let q_ast = z3.rational(q)?;
            z3.eq(r, q_ast)
        }
        ORoot::Interval(lo, hi) => {
            let lo_ast = z3.rational(lo)?;
            let hi_ast = z3.rational(hi)?;
            Some(z3.gt(r, lo_ast)? && z3.lt(r, hi_ast)?)
        }
    }
}

fn describe_marker(m: &ORoot) -> String {
    match m {
        ORoot::Rational(r) => format!("exact {r}"),
        ORoot::Interval(lo, hi) => format!("({lo}, {hi})"),
    }
}

/// Real-root isolation: AY's markers vs z3's algebraic roots.
pub(crate) fn check_roots(z3: &Z3, p: &GenPoly, sab: Sabotage) -> Outcome {
    let ap = poly_of(p);
    if ap.degree().unwrap_or(0) < 1 {
        return Outcome::Skipped("degree < 1");
    }
    let Some(sf) = ap.square_free_part() else {
        return Outcome::Declined("square_free_part");
    };
    let Some(mut markers) = sf.isolate_roots() else {
        return Outcome::Declined("isolate_roots");
    };
    if sab.on() {
        // Drop a root AY did find; the count comparison must notice.
        if markers.pop().is_none() {
            return Outcome::Skipped("nothing to sabotage");
        }
    }
    let Some(roots) = z3.roots(&p.coeffs) else {
        return Outcome::Skipped("z3 declined");
    };
    if markers.len() != roots.len() {
        return Divergence::outcome(
            "roots",
            "z3",
            format!(
                "AY isolated {} real roots, z3 found {}",
                markers.len(),
                roots.len()
            ),
            inputs1(p),
        );
    }
    let mut comparisons = 1u64;
    for (i, (m, r)) in markers.iter().zip(roots.iter()).enumerate() {
        comparisons += 1;
        let Some(matches) = marker_matches(z3, m, *r) else {
            return Outcome::Skipped("z3 errored while checking a root marker");
        };
        if !matches {
            let bracket = z3.bracket(*r, 64).map_or_else(
                || "<unbracketable>".to_string(),
                |(lo, hi)| format!("({lo}, {hi})"),
            );
            return Divergence::outcome(
                "roots",
                "z3",
                format!(
                    "root #{i}: AY marker {} does not contain z3's root, which lies in {bracket}",
                    describe_marker(m)
                ),
                inputs1(p),
            );
        }
    }
    Outcome::Match(comparisons)
}

/// The square-free part must have exactly the same real roots as the original,
/// and must divide it.
fn square_free_identity(ap: &OPoly, sf: &OPoly, p: &GenPoly) -> Option<Outcome> {
    // Exact algebraic identity: the square-free part divides the polynomial.
    if !sf.is_zero() && !ap.rem(sf).is_zero() {
        return Some(Divergence::outcome(
            "square-free",
            "identity",
            format!(
                "square_free_part {} does not divide p",
                polygen::render(&sf.coeffs())
            ),
            inputs1(p),
        ));
    }
    // THE PROPERTY THE NAME PROMISES: `sf` must actually BE square-free, i.e.
    // `gcd(sf, sf')` is a non-zero constant.
    //
    // Without this the check is strictly weaker than what its consumers rely on,
    // and provably so: the two assertions around it — "`sf` divides `p`" and
    // "`p` and `sf` have the same distinct real roots" — BOTH hold trivially for
    // a `square_free_part` that returns `p` UNCHANGED, because stripping
    // repeated factors changes multiplicities, never the root SET. An adversary
    // injected exactly that defect and this check reported ZERO divergences over
    // 4,000 cases; only 3 incidental hits leaked out through sturm-count and
    // algebraic-compare.
    //
    // That matters because square-freeness is a PRECONDITION of `isolate_roots`
    // and of nlsat projection — the code the B1 port is being built against. An
    // oracle blind to it would license the port's most load-bearing assumption.
    if !sf.is_zero() {
        let d = sf.derivative();
        if !d.is_zero() {
            let g = sf.gcd(&d);
            if g.degree().unwrap_or(0) >= 1 {
                return Some(Divergence::outcome(
                    "square-free",
                    "identity",
                    format!(
                        "square_free_part is NOT square-free: gcd(sf, sf') has degree {} (sf = {}, gcd = {})",
                        g.degree().unwrap_or(0),
                        polygen::render(&sf.coeffs()),
                        polygen::render(&g.coeffs())
                    ),
                    inputs1(p),
                ));
            }
        }
    }
    None
}

fn compare_square_free_roots(z3: &Z3, p: &GenPoly, sf: OPoly) -> Outcome {
    let sf_coeffs = sf.coeffs();
    let (Some(rp), Some(rs)) = (z3.roots(&p.coeffs), z3.roots(&sf_coeffs)) else {
        return Outcome::Skipped("z3 declined");
    };
    if rp.len() != rs.len() {
        return Divergence::outcome(
            "square-free",
            "z3",
            format!(
                "p has {} distinct real roots but AY's square-free part has {} (sf = {})",
                rp.len(),
                rs.len(),
                polygen::render(&sf_coeffs)
            ),
            inputs1(p),
        );
    }
    let mut comparisons = 1u64;
    for (i, (a, b)) in rp.iter().zip(rs.iter()).enumerate() {
        comparisons += 1;
        let Some(equal) = z3.eq(*a, *b) else {
            return Outcome::Skipped("z3 errored while comparing roots");
        };
        if !equal {
            let ba = z3.bracket(*a, 60).map_or_else(
                || "?".to_string(),
                |(lo, hi)| format!("({}, {})", to_f64(&lo), to_f64(&hi)),
            );
            let bb = z3.bracket(*b, 60).map_or_else(
                || "?".to_string(),
                |(lo, hi)| format!("({}, {})", to_f64(&lo), to_f64(&hi)),
            );
            let mut inp = inputs1(p);
            inp.push(("sf".to_string(), polygen::render(&sf_coeffs)));
            inp.push(("p.root".to_string(), ba));
            inp.push(("sf.root".to_string(), bb));
            return Divergence::outcome(
                "square-free",
                "z3",
                format!("root #{i} of p differs from root #{i} of AY's square-free part"),
                inp,
            );
        }
    }
    Outcome::Match(comparisons)
}

pub(crate) fn check_square_free(z3: &Z3, p: &GenPoly, sab: Sabotage) -> Outcome {
    let ap = poly_of(p);
    if ap.degree().unwrap_or(0) < 1 {
        return Outcome::Skipped("degree < 1");
    }
    let Some(sf) = ap.square_free_part() else {
        return Outcome::Declined("square_free_part");
    };
    if !sab.on() {
        if let Some(outcome) = square_free_identity(&ap, &sf, p) {
            return outcome;
        }
    }
    // Sabotage hands the root comparison a square-free part with one extra
    // real root.
    let compared = if sab.on() {
        sf.mul(&saboteur_factor())
    } else {
        sf
    };
    compare_square_free_roots(z3, p, compared)
}

/// Decimal rendering of a rational, for human-readable reproducer dumps only.
/// Nothing in the oracle's decision path ever touches a float.
fn to_f64(r: &BigRational) -> String {
    let n = r.numer().to_string().parse::<f64>().unwrap_or(f64::NAN);
    let d = r.denom().to_string().parse::<f64>().unwrap_or(f64::NAN);
    format!("{:.12}", n / d)
}

/// GCD: must divide both inputs, and its real roots must be exactly the roots
/// shared by both inputs (z3's verdict on both root sets).
pub(crate) fn check_gcd(z3: &Z3, p: &GenPoly, q: &GenPoly, sab: Sabotage) -> Outcome {
    let (ap, aq) = (poly_of(p), poly_of(q));
    if ap.degree().unwrap_or(0) < 1 || aq.degree().unwrap_or(0) < 1 {
        return Outcome::Skipped("degree < 1");
    }
    let g = ap.gcd(&aq);
    if g.is_zero() {
        return Divergence::outcome(
            "gcd",
            "identity",
            "gcd of two non-zero polynomials is zero".to_string(),
            inputs2(p, q),
        );
    }
    if !ap.rem(&g).is_zero() || !aq.rem(&g).is_zero() {
        return Divergence::outcome(
            "gcd",
            "identity",
            format!(
                "gcd {} does not divide both inputs",
                polygen::render(&g.coeffs())
            ),
            inputs2(p, q),
        );
    }
    // Sabotage: claim a shared factor that is not there.
    let g = if sab.on() {
        g.mul(&saboteur_factor())
    } else {
        g
    };
    let g_coeffs = g.coeffs();
    let (Some(rp), Some(rq)) = (z3.roots(&p.coeffs), z3.roots(&q.coeffs)) else {
        return Outcome::Skipped("z3 declined");
    };
    // z3's view of the shared real roots.
    let mut shared: Vec<Ast> = Vec::new();
    let mut comparisons = 0u64;
    for a in &rp {
        for b in &rq {
            comparisons += 1;
            let Some(equal) = z3.eq(*a, *b) else {
                return Outcome::Skipped("z3 errored while comparing roots");
            };
            if equal {
                shared.push(*a);
                break;
            }
        }
    }
    let rg = if g.degree().unwrap_or(0) < 1 {
        Vec::new()
    } else {
        match z3.roots(&g_coeffs) {
            Some(v) => v,
            None => return Outcome::Skipped("z3 declined"),
        }
    };
    if rg.len() != shared.len() {
        return Divergence::outcome(
            "gcd",
            "z3",
            format!(
                "AY's gcd {} has {} real roots but p and q share {}",
                polygen::render(&g_coeffs),
                rg.len(),
                shared.len()
            ),
            inputs2(p, q),
        );
    }
    for (i, (a, b)) in rg.iter().zip(shared.iter()).enumerate() {
        comparisons += 1;
        let Some(equal) = z3.eq(*a, *b) else {
            return Outcome::Skipped("z3 errored while comparing roots");
        };
        if !equal {
            return Divergence::outcome(
                "gcd",
                "z3",
                format!("shared root #{i} differs from root #{i} of AY's gcd"),
                inputs2(p, q),
            );
        }
    }
    Outcome::Match(comparisons + 1)
}

/// Sturm's theorem: AY's root count on `(a, b]` vs counting z3's roots.
pub(crate) fn check_sturm(
    z3: &Z3,
    p: &GenPoly,
    mut a: BigRational,
    mut b: BigRational,
    sab: Sabotage,
) -> Outcome {
    let ap = poly_of(p);
    if ap.degree().unwrap_or(0) < 1 {
        return Outcome::Skipped("degree < 1");
    }
    if a > b {
        std::mem::swap(&mut a, &mut b);
    }
    if a == b {
        return Outcome::Skipped("empty interval");
    }
    let Some(sf) = ap.square_free_part() else {
        return Outcome::Declined("square_free_part");
    };
    if sf.degree().unwrap_or(0) < 1 {
        return Outcome::Skipped("square-free part is constant");
    }
    // Sabotage: an off-by-one in the root count.
    let ay_count = sf.sturm_count_in(&a, &b) + usize::from(sab.on());
    let Some(roots) = z3.roots(&p.coeffs) else {
        return Outcome::Skipped("z3 declined");
    };
    let (Some(a_ast), Some(b_ast)) = (z3.rational(&a), z3.rational(&b)) else {
        return Outcome::Skipped("z3 rejected a rational interval endpoint");
    };
    // Sturm counts the half-open interval (a, b].
    let mut z3_count = 0;
    for root in roots {
        let (Some(above_a), Some(above_b)) = (z3.gt(root, a_ast), z3.gt(root, b_ast)) else {
            return Outcome::Skipped("z3 errored while ordering roots");
        };
        z3_count += usize::from(above_a && !above_b);
    }
    if ay_count != z3_count {
        return Divergence::outcome(
            "sturm-count",
            "z3",
            format!("AY counts {ay_count} roots in ({a}, {b}], z3 counts {z3_count}"),
            inputs1(p),
        );
    }
    Outcome::Match(1)
}

/// Sign of a polynomial at a real algebraic point.
pub(crate) fn check_sign_at(
    z3: &Z3,
    p: &GenPoly,
    q: &GenPoly,
    pick: u64,
    sab: Sabotage,
) -> Outcome {
    let ap = poly_of(p);
    if ap.degree().unwrap_or(0) < 1 {
        return Outcome::Skipped("degree < 1");
    }
    let Some(sf) = ap.square_free_part() else {
        return Outcome::Declined("square_free_part");
    };
    let Some(markers) = sf.isolate_roots() else {
        return Outcome::Declined("isolate_roots");
    };
    if markers.is_empty() {
        return Outcome::Skipped("no real roots");
    }
    let Some(roots) = z3.roots(&p.coeffs) else {
        return Outcome::Skipped("z3 declined");
    };
    if roots.len() != markers.len() {
        // Root-count disagreement is `check_roots`' business; do not
        // double-report it here.
        return Outcome::Skipped("root counts differ (see roots check)");
    }
    let idx = usize::try_from(pick).unwrap_or(0) % markers.len();
    let aq = poly_of(q);
    let Some(z3_sign) = z3.eval_sign(&q.coeffs, roots[idx]) else {
        return Outcome::Skipped("z3 declined");
    };

    let (ay_sign, path) = match &markers[idx] {
        ORoot::Rational(r) => {
            // Rational root: AY evaluates exactly, no refinement involved.
            (ay::sign_of(&aq.eval(r)), "rational-eval")
        }
        ORoot::Interval(lo, hi) => {
            let Some(alpha) = OAlg::new(&sf, lo, hi) else {
                return Outcome::Declined("OAlg::new");
            };
            // Cross-check AY against itself: the root index it derives by Sturm
            // counting must be this marker's position in ascending order.
            if alpha.root_index() != idx + 1 {
                return Divergence::outcome(
                    "sign-at-algebraic",
                    "identity",
                    format!(
                        "AY's derived root index is {} but the marker is #{} in ascending order",
                        alpha.root_index(),
                        idx + 1
                    ),
                    inputs2(p, q),
                );
            }
            match alpha.sign_of_poly(&aq) {
                Some(s) => (s, "sign_of_poly"),
                None => return Outcome::Declined("sign_of_poly"),
            }
        }
    };
    // Sabotage: flip the sign (a zero becomes a positive).
    let ay_sign = if sab.on() {
        if ay_sign == 0 {
            1
        } else {
            -ay_sign
        }
    } else {
        ay_sign
    };
    if ay_sign.signum() != z3_sign.signum() {
        return Divergence::outcome(
            "sign-at-algebraic",
            "z3",
            format!(
                "at root #{idx} of p, AY says sign(q) = {ay_sign} ({path}) but z3 says {z3_sign}"
            ),
            inputs2(p, q),
        );
    }
    Outcome::Match(1)
}
