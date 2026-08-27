// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bivariate subresultant checks by specialization.

use super::*;

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
        return Divergence::outcome(
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
        return Divergence::outcome(
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
