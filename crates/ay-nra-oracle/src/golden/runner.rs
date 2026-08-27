// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Included by the parent module to keep fixture order explicit.

/// Run every fixture. When `z3` is supplied, each root fixture is ALSO checked
/// live against the reference implementation, so a stale hand-written
/// expectation cannot mask a real disagreement.
fn run_root_checks(z3: Option<&Z3>, include_heavy: bool) -> Vec<GoldenResult> {
    let mut out = Vec::new();

    for f in root_fixtures() {
        if f.heavy && !include_heavy {
            continue;
        }
        let p = OPoly::from_coeffs(f.coeffs.clone());
        let Some(sf) = p.square_free_part() else {
            out.push(fail(f.name, "AY declined square_free_part".to_string()));
            continue;
        };
        let Some(markers) = sf.isolate_roots() else {
            out.push(fail(f.name, "AY declined isolate_roots".to_string()));
            continue;
        };
        match check_expected_roots(&markers, &f.expected) {
            Ok(()) => out.push(pass(f.name)),
            Err(e) => out.push(fail(f.name, e)),
        }
        if let Some(z) = z3 {
            let name = format!("{} [live z3]", f.name);
            match z.roots(&f.coeffs) {
                None => out.push(fail(&name, "z3 declined".to_string())),
                Some(roots) => {
                    if roots.len() != markers.len() {
                        out.push(fail(
                            &name,
                            format!("z3 found {} roots, AY {}", roots.len(), markers.len()),
                        ));
                    } else {
                        let mut ok = true;
                        let mut z3_failed = false;
                        for (m, r) in markers.iter().zip(roots.iter()) {
                            let hit = match m {
                                ORoot::Rational(q) => z.rational(q).and_then(|a| z.eq(*r, a)),
                                ORoot::Interval(lo, hi) => {
                                    let Some(a) = z.rational(lo) else {
                                        z3_failed = true;
                                        break;
                                    };
                                    let Some(b) = z.rational(hi) else {
                                        z3_failed = true;
                                        break;
                                    };
                                    match (z.gt(*r, a), z.lt(*r, b)) {
                                        (Some(above), Some(below)) => Some(above && below),
                                        _ => None,
                                    }
                                }
                            };
                            match hit {
                                Some(true) => {}
                                Some(false) => {
                                    ok = false;
                                    break;
                                }
                                None => {
                                    z3_failed = true;
                                    break;
                                }
                            }
                        }
                        if z3_failed {
                            out.push(fail(
                                &name,
                                "z3 errored while checking AY's root markers".to_string(),
                            ));
                        } else if ok {
                            out.push(pass(&name));
                        } else {
                            out.push(fail(
                                &name,
                                format!(
                                    "AY markers {} do not localize z3's roots",
                                    render_markers(&markers)
                                ),
                            ));
                        }
                    }
                }
            }
        }
    }

    out
}

fn run_gcd_checks(include_heavy: bool) -> Vec<GoldenResult> {
    let mut out = Vec::new();
    for mut f in gcd_fixtures() {
        if f.heavy && !include_heavy {
            continue;
        }
        if f.q.is_empty() {
            f.q = OPoly::from_coeffs(f.p.clone()).derivative().coeffs();
        }
        let p = OPoly::from_coeffs(f.p.clone());
        let q = OPoly::from_coeffs(f.q.clone());
        let g = p.gcd(&q);
        let want = OPoly::from_coeffs(f.expected.clone());
        // Compare up to a rational scale: both monic-normalized.
        let ok = match (g.degree(), want.degree()) {
            (Some(a), Some(b)) if a == b => {
                let gl = g.coeffs().last().cloned();
                let wl = want.coeffs().last().cloned();
                match (gl, wl) {
                    (Some(gl), Some(wl)) => {
                        let gn = g.scale(&(BigRational::one() / gl));
                        let wn = want.scale(&(BigRational::one() / wl));
                        gn.coeffs() == wn.coeffs()
                    }
                    _ => false,
                }
            }
            _ => false,
        };
        if ok {
            out.push(pass(f.name));
        } else {
            out.push(fail(
                f.name,
                format!(
                    "AY gcd = {}, expected (up to scale) {}",
                    polygen::render(&g.coeffs()),
                    polygen::render(&f.expected)
                ),
            ));
        }
    }

    out
}

fn run_resultant_checks(z3: Option<&Z3>) -> Vec<GoldenResult> {
    let mut out = Vec::new();
    for f in res_fixtures() {
        let p = OPoly::from_coeffs(f.p.clone());
        let q = OPoly::from_coeffs(f.q.clone());
        match ay_nra::oracle_api::resultant(&p, &q) {
            None => out.push(fail(f.name, "AY declined resultant".to_string())),
            Some(r) if r == f.expected => out.push(pass(f.name)),
            Some(r) => out.push(fail(
                f.name,
                format!("AY resultant = {r}, expected {}", f.expected),
            )),
        }
        if let Some(z) = z3 {
            let name = format!("{} [live z3 psc]", f.name);
            match z.subresultants(&f.p, &f.q) {
                None => out.push(fail(&name, "z3 declined".to_string())),
                Some(chain) => {
                    let rendered: Vec<String> = chain
                        .iter()
                        .map(|a| {
                            z.numeral_value(*a).map_or_else(
                                || {
                                    z.ast_string(*a)
                                        .unwrap_or_else(|| "<invalid-z3-ast>".into())
                                },
                                |v| v.to_string(),
                            )
                        })
                        .collect();
                    out.push(GoldenResult {
                        name,
                        passed: true,
                        detail: format!("psc chain = [{}]", rendered.join(", ")),
                    });
                }
            }
        }
    }

    out
}

fn run_algebraic_sign_check() -> Vec<GoldenResult> {
    let mut out = Vec::new();
    // Sign of a polynomial at an irrational algebraic point, the univariate
    // core of `algebraic.cpp::tst_eval_sign`.
    {
        let name = "algebraic/sign at sqrt(2)";
        let p = OPoly::from_coeffs(ipoly(&[-2, 0, 1])); // x^2 - 2
        let alpha = OAlg::new(&p, &rat(1, 1), &rat(2, 1));
        match alpha {
            None => out.push(fail(name, "AY declined OAlg::new".to_string())),
            Some(a) => {
                let cases: [(&str, Vec<BigRational>, i32); 4] = [
                    ("x^2-2", ipoly(&[-2, 0, 1]), 0),
                    ("x^2-3", ipoly(&[-3, 0, 1]), -1),
                    ("x-1", ipoly(&[-1, 1]), 1),
                    ("2x-3", ipoly(&[-3, 2]), -1),
                ];
                let mut bad = Vec::new();
                for (label, coeffs, want) in cases {
                    let got = a.sign_of_poly(&OPoly::from_coeffs(coeffs));
                    if got != Some(want) {
                        bad.push(format!("{label}: got {got:?}, want {want}"));
                    }
                }
                if bad.is_empty() {
                    out.push(pass(name));
                } else {
                    out.push(fail(name, bad.join("; ")));
                }
            }
        }
    }

    out
}

fn run_modular_gcd_checks() -> Vec<GoldenResult> {
    let mut out = Vec::new();
    // The modular GCD must still certify every multivariate shape.
    //
    // This fixture exists because a verifier proved the differential oracle is
    // structurally BLIND to a total regression of the modular path: a one-token
    // swap of the returned tuple in `zp_cont_pp_y` collapsed certification from
    // 100% to 25.5% — 0 of 5 shapes — and `fuzz` reported DIVERGENCES 0. Every
    // check still passed, because declining is not diverging: a decline is
    // safe, `PolyManager::gcd` falls back to the PRS, and every answer stays
    // correct. Nothing anywhere asserted that the fast path still WORKS.
    //
    // So the achievement is pinned here rather than in a fuzz check. It is not
    // a soundness gate — it is a performance gate, and the only reason it
    // belongs in the golden corpus is that a silent regression to a 20-second
    // gcd is exactly as fatal to a competition score as a wrong answer.
    for i in 0..pmgr::mv_shape_count() {
        let r = pmgr::measure_mv_cost(i);
        let name = format!("mod_gcd certifies `{}`", r.label);
        if !r.mod_certified {
            out.push(fail(
                &name,
                format!(
                    "the modular gcd DECLINED on a {}-term/{}-term shape; the PRS fallback \
                     took {} ms. The fast path has regressed — see \
                     the development design notes",
                    r.u_terms, r.v_terms, r.prs_ms
                ),
            ));
        } else if r.agreed {
            out.push(pass(&name));
        } else {
            out.push(fail(
                &name,
                "the modular gcd certified an answer that DISAGREES with the subresultant PRS"
                    .to_string(),
            ));
        }
    }

    out
}

/// Run every fixture, preserving the stable fixture-family output order.
pub(crate) fn run_all(z3: Option<&Z3>, include_heavy: bool) -> Vec<GoldenResult> {
    let mut out = run_root_checks(z3, include_heavy);
    out.extend(run_gcd_checks(include_heavy));
    out.extend(run_resultant_checks(z3));
    out.extend(run_algebraic_sign_check());
    out.extend(run_modular_gcd_checks());
    out
}

#[cfg(test)]
mod tests {
    use super::run_all;

    /// The AY-only half of the golden corpus runs with no z3 present, so a
    /// plain `cargo test` regresses the fixtures on any machine.
    ///
    /// The heavy fixtures — Wilkinson-20, the degree-17 sparse polynomial and
    /// `(x^5 - 10^9)^3 (3x - 10^7)^2 (10x - 632)^2` — are included: measured
    /// 0.7s for the whole set, which is cheap enough to keep in the default
    /// test run rather than behind a flag nobody remembers to pass.
    #[test]
    fn golden_fixtures_pass_without_z3() {
        let results = run_all(None, true);
        let failures: Vec<String> = results
            .iter()
            .filter(|r| !r.passed)
            .map(|r| format!("{}: {}", r.name, r.detail))
            .collect();
        assert!(
            results.len() >= 20,
            "expected the full corpus, got {}",
            results.len()
        );
        assert!(
            failures.is_empty(),
            "golden failures:\n{}",
            failures.join("\n")
        );
    }
}
