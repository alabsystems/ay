// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Included by the parent module to preserve the oracle API paths.

// ---------------------------------------------------------------------------
// Building the shared sample point
// ---------------------------------------------------------------------------

/// One coordinate, as both sides see it.
struct Coord {
    ay: OAnum,
    z3: Ast,
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
fn build_poly(z3: &Z3, g: &GenMv) -> Option<(OMPoly, Ast)> {
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
fn agrees(z3: &Z3, v: Ast, ay: &OAnum) -> Option<bool> {
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
    let values: Vec<Ast> = coords.iter().map(|c| c.z3).collect();
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
        return Divergence::outcome(
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
            return Divergence::outcome(
                "mv-isolate-roots",
                "z3",
                format!(
                    "root #{} disagrees: z3 says {}, AY's value is not in that enclosure",
                    i + 1,
                    z3.ast_string(*v)
                        .unwrap_or_else(|| "<invalid-z3-ast>".into())
                ),
                inputs(g),
            );
        }
    }
    Outcome::Match(comparisons)
}
