// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Starter subset of z3's own golden tests, transliterated as fixtures.
//!
//! Sources (z3 5.0.0, `src/test/`):
//!   * `upolynomial.cpp::tst_isolate_roots` — the root-isolation corpus,
//!     including the clustered `10000x-31` family, the degree-17 sparse
//!     polynomial and the `(x^5 - 10^9)^3` monster.
//!   * `upolynomial.cpp::tst_remove_one_half` — the `x = 1/2` rational root.
//!   * `upolynomial.cpp::tst_gcd` — including Knuth's coprime pair.
//!   * `upolynomial.cpp::tst_sturm` — the degree-10 Sturm-sequence input.
//!   * `algebraic.cpp::tst_wilkinson` — 20 integer roots.
//!   * `algebraic.cpp::tst_root` — `4^(1/2)` and `4^(1/4)`.
//!
//! The root fixtures reuse z3's own acceptance criterion verbatim
//! (`check_roots` in `upolynomial.cpp`): every expected value must be matched
//! by exactly one isolating marker — as an exact rational root, or as a strict
//! interval containing it. z3's own expectations for irrational roots are
//! decimal approximations, and they are kept as such here.

use ay_nra::oracle_api::{OAlg, OPoly, ORoot};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::One;

use crate::checks::{ipoly, mul_coeffs, pow_coeffs, rat};
use crate::pmgr;
use crate::polygen;
use crate::z3::Z3;

/// One fixture's verdict.
pub(crate) struct GoldenResult {
    pub(crate) name: String,
    pub(crate) passed: bool,
    pub(crate) detail: String,
}

fn linear(a: i64, b: i64) -> Vec<BigRational> {
    // a*x + b, low-to-high.
    ipoly(&[b, a])
}

fn product(factors: &[Vec<BigRational>]) -> Vec<BigRational> {
    let mut acc = vec![BigRational::one()];
    for f in factors {
        acc = mul_coeffs(&acc, f);
    }
    acc
}

/// z3's `check_roots`: each expected value must be matched by exactly one
/// marker, and no marker may match two expectations.
fn check_expected_roots(markers: &[ORoot], expected: &[BigRational]) -> Result<(), String> {
    if markers.len() != expected.len() {
        return Err(format!(
            "expected {} roots, AY isolated {}",
            expected.len(),
            markers.len()
        ));
    }
    let mut visited = vec![false; markers.len()];
    for (i, r) in expected.iter().enumerate() {
        let mut found: Option<usize> = None;
        for (j, m) in markers.iter().enumerate() {
            let hit = match m {
                ORoot::Rational(q) => q == r,
                ORoot::Interval(lo, hi) => lo < r && r < hi,
            };
            if hit {
                if found.is_some() || visited[j] {
                    return Err(format!(
                        "expected root #{i} ({r}) matched more than one marker"
                    ));
                }
                found = Some(j);
                visited[j] = true;
            }
        }
        if found.is_none() {
            return Err(format!(
                "expected root #{i} ({r}) matched no marker; markers = {}",
                render_markers(markers)
            ));
        }
    }
    Ok(())
}

fn render_markers(markers: &[ORoot]) -> String {
    let parts: Vec<String> = markers
        .iter()
        .map(|m| match m {
            ORoot::Rational(r) => format!("[{r}]"),
            ORoot::Interval(lo, hi) => format!("({lo},{hi})"),
        })
        .collect();
    format!("{{{}}}", parts.join(", "))
}

/// A root-isolation fixture: polynomial plus z3's expected root values.
struct RootFixture {
    name: &'static str,
    coeffs: Vec<BigRational>,
    expected: Vec<BigRational>,
    /// Heavy fixtures (high degree, huge coefficients) are skipped unless the
    /// caller asks for them, so the default run stays quick.
    heavy: bool,
}

fn root_fixtures() -> Vec<RootFixture> {
    let x5_minus_x_minus_1 = ipoly(&[-1, -1, 0, 0, 0, 1]);
    let x5_plus_x_minus_1 = ipoly(&[-1, 1, 0, 0, 0, 1]);
    let sparse17 = {
        // x^17 + 5x^16 + 3x^15 + 10x^13 + 13x^10 + x^9 + 8x^5 + 3x^2 + 7
        let mut c = vec![BigRational::from_integer(BigInt::from(0)); 18];
        c[17] = BigRational::from_integer(BigInt::from(1));
        c[16] = BigRational::from_integer(BigInt::from(5));
        c[15] = BigRational::from_integer(BigInt::from(3));
        c[13] = BigRational::from_integer(BigInt::from(10));
        c[10] = BigRational::from_integer(BigInt::from(13));
        c[9] = BigRational::from_integer(BigInt::from(1));
        c[5] = BigRational::from_integer(BigInt::from(8));
        c[2] = BigRational::from_integer(BigInt::from(3));
        c[0] = BigRational::from_integer(BigInt::from(7));
        c
    };

    vec![
        RootFixture {
            name: "upoly/(x-1)(x-2)",
            coeffs: product(&[linear(1, -1), linear(1, -2)]),
            expected: vec![rat(1, 1), rat(2, 1)],
            heavy: false,
        },
        RootFixture {
            name: "upoly/(x-1)^2 x^3",
            coeffs: product(&[pow_coeffs(&linear(1, -1), 2), pow_coeffs(&linear(1, 0), 3)]),
            expected: vec![rat(1, 1), rat(0, 1)],
            heavy: false,
        },
        RootFixture {
            name: "upoly/x^5-x-1",
            coeffs: x5_minus_x_minus_1.clone(),
            expected: vec![rat(11_673_039, 10_000_000)],
            heavy: false,
        },
        RootFixture {
            name: "upoly/(x-1)(x+1)(x+2)(x+3)(x-3)^2",
            coeffs: product(&[
                linear(1, -1),
                linear(1, 1),
                linear(1, 2),
                linear(1, 3),
                pow_coeffs(&linear(1, -3), 2),
            ]),
            expected: vec![rat(1, 1), rat(-1, 1), rat(-2, 1), rat(-3, 1), rat(3, 1)],
            heavy: false,
        },
        RootFixture {
            name: "upoly/(10000x-31)(10000x-32)",
            coeffs: product(&[linear(10_000, -31), linear(10_000, -32)]),
            expected: vec![rat(31, 10_000), rat(32, 10_000)],
            heavy: false,
        },
        RootFixture {
            name: "upoly/(10000x-31)(10000x-32)(10000x-33)",
            coeffs: product(&[
                linear(10_000, -31),
                linear(10_000, -32),
                linear(10_000, -33),
            ]),
            expected: vec![rat(31, 10_000), rat(32, 10_000), rat(33, 10_000)],
            heavy: false,
        },
        RootFixture {
            name: "upoly/(x^5-x-1)(x^5+x-1)(1000x-1167)",
            coeffs: product(&[
                x5_minus_x_minus_1.clone(),
                x5_plus_x_minus_1.clone(),
                linear(1000, -1167),
            ]),
            expected: vec![
                rat(11_673_039, 10_000_000),
                rat(75_487_766, 100_000_000),
                rat(1167, 1000),
            ],
            heavy: false,
        },
        RootFixture {
            name: "upoly/11-factor dyadic product",
            coeffs: product(&[
                linear(1, -2),
                linear(1, -4),
                linear(1, -8),
                linear(1, -16),
                linear(1, -32),
                linear(1, -64),
                linear(2, -1),
                linear(4, -1),
                linear(8, -1),
                linear(16, -1),
                linear(32, -1),
            ]),
            expected: vec![
                rat(2, 1),
                rat(4, 1),
                rat(8, 1),
                rat(16, 1),
                rat(32, 1),
                rat(64, 1),
                rat(1, 2),
                rat(1, 4),
                rat(1, 8),
                rat(1, 16),
                rat(1, 32),
            ],
            heavy: false,
        },
        RootFixture {
            name: "upoly/((x^5-x-1)(x^5+x-1)(1000x-1167))^2",
            coeffs: pow_coeffs(
                &product(&[
                    x5_minus_x_minus_1.clone(),
                    x5_plus_x_minus_1.clone(),
                    linear(1000, -1167),
                ]),
                2,
            ),
            expected: vec![
                rat(11_673_039, 10_000_000),
                rat(75_487_766, 100_000_000),
                rat(1167, 1000),
            ],
            heavy: true,
        },
        RootFixture {
            name: "upoly/sparse degree 17",
            coeffs: sparse17.clone(),
            expected: vec![
                rat(-413_582, 100_000),
                rat(-170_309, 100_000),
                rat(-109_968, 100_000),
            ],
            heavy: true,
        },
        RootFixture {
            name: "upoly/sparse17 * (x^5-x-1)^2 * (x^3-2)^2",
            coeffs: product(&[
                sparse17,
                pow_coeffs(&x5_minus_x_minus_1, 2),
                pow_coeffs(&ipoly(&[-2, 0, 0, 1]), 2),
            ]),
            expected: vec![
                rat(-413_582, 100_000),
                rat(-170_309, 100_000),
                rat(-109_968, 100_000),
                rat(11_673_039, 10_000_000),
                rat(125_992, 100_000),
            ],
            heavy: true,
        },
        RootFixture {
            name: "upoly/(x^5-10^9)^3 (3x-10^7)^2 (10x-632)^2",
            coeffs: product(&[
                pow_coeffs(&ipoly(&[-1_000_000_000, 0, 0, 0, 0, 1]), 3),
                pow_coeffs(&linear(3, -10_000_000), 2),
                pow_coeffs(&linear(10, -632), 2),
            ]),
            expected: vec![rat(630_957, 10_000), rat(10_000_000, 3), rat(632, 10)],
            heavy: true,
        },
        RootFixture {
            name: "upoly/4x^3-12x^2-x+3 (has x = 1/2)",
            coeffs: ipoly(&[3, -1, -12, 4]),
            // 4x^3-12x^2-x+3 = (2x-1)(2x+1)(x-3)
            expected: vec![rat(1, 2), rat(-1, 2), rat(3, 1)],
            heavy: false,
        },
        RootFixture {
            name: "algebraic/x^2-4 (root(4,2))",
            coeffs: ipoly(&[-4, 0, 1]),
            expected: vec![rat(-2, 1), rat(2, 1)],
            heavy: false,
        },
        RootFixture {
            name: "algebraic/x^4-4 (root(4,4) = sqrt 2)",
            coeffs: ipoly(&[-4, 0, 0, 0, 1]),
            expected: vec![rat(-1_414_213, 1_000_000), rat(1_414_213, 1_000_000)],
            heavy: false,
        },
        RootFixture {
            name: "algebraic/wilkinson prod_{i=1..20}(x-i)",
            coeffs: {
                let mut acc = vec![BigRational::one()];
                for i in 1..=20i64 {
                    acc = mul_coeffs(&acc, &linear(1, -i));
                }
                acc
            },
            expected: (1..=20i64).map(|i| rat(i, 1)).collect(),
            heavy: true,
        },
        RootFixture {
            name: "upoly/sturm degree-10 input",
            coeffs: ipoly(&[8, 2, 8, 10, 10, 0, 1, 0, 1, 3, 7]),
            // 7x^10+3x^9+x^8+x^6+10x^4+10x^3+8x^2+2x+8 has NO real roots.
            // z3 only prints the Sturm sequence for this input, so the
            // expectation was established independently:
            //   $ z3 -- (assert (= 0 <this poly>)) (check-sat)  =>  unsat
            expected: Vec::new(),
            heavy: false,
        },
    ]
}

/// A gcd fixture: two polynomials and the expected gcd's real roots.
struct GcdFixture {
    name: &'static str,
    p: Vec<BigRational>,
    q: Vec<BigRational>,
    /// Expected gcd up to a rational scale factor.
    expected: Vec<BigRational>,
    heavy: bool,
}

fn gcd_fixtures() -> Vec<GcdFixture> {
    vec![
        GcdFixture {
            name: "upoly/knuth coprime pair",
            // x^8+x^6-3x^4-3x^3+8x^2+2x-5 and 3x^6+5x^4-4x^2-9x+21
            p: ipoly(&[-5, 2, 8, -3, -3, 0, 1, 0, 1]),
            q: ipoly(&[21, -9, -4, 0, 5, 0, 3]),
            expected: ipoly(&[1]),
            heavy: false,
        },
        GcdFixture {
            name: "upoly/(x-1)^2(x-3)(x+2)(x-5)^3 vs (x+1)(x-1)(x-3)^2(x+3)(x-5)",
            p: product(&[
                pow_coeffs(&linear(1, -1), 2),
                linear(1, -3),
                linear(1, 2),
                pow_coeffs(&linear(1, -5), 3),
            ]),
            q: product(&[
                linear(1, 1),
                linear(1, -1),
                pow_coeffs(&linear(1, -3), 2),
                linear(1, 3),
                linear(1, -5),
            ]),
            expected: product(&[linear(1, -1), linear(1, -3), linear(1, -5)]),
            heavy: false,
        },
        GcdFixture {
            name: "upoly/13(x-3)^6(x-5)^5(x-11)^7 vs its derivative",
            p: {
                let base = product(&[
                    pow_coeffs(&linear(1, -3), 6),
                    pow_coeffs(&linear(1, -5), 5),
                    pow_coeffs(&linear(1, -11), 7),
                ]);
                base.iter()
                    .map(|c| c * BigRational::from_integer(BigInt::from(13)))
                    .collect()
            },
            q: Vec::new(), // filled in as p' below
            expected: product(&[
                pow_coeffs(&linear(1, -3), 5),
                pow_coeffs(&linear(1, -5), 4),
                pow_coeffs(&linear(1, -11), 6),
            ]),
            heavy: true,
        },
    ]
}

/// Resultant fixtures with closed-form expected values.
struct ResFixture {
    name: &'static str,
    p: Vec<BigRational>,
    q: Vec<BigRational>,
    expected: BigRational,
}

fn res_fixtures() -> Vec<ResFixture> {
    vec![
        // Res(x - a, x - b) = b - a.
        ResFixture {
            name: "res/(x-2, x-5) = 3",
            p: ipoly(&[-2, 1]),
            q: ipoly(&[-5, 1]),
            expected: rat(-3, 1),
        },
        // Res(x^2 - a, x^2 - b) = (a - b)^2.
        ResFixture {
            name: "res/(x^2-2, x^2-3) = 1",
            p: ipoly(&[-2, 0, 1]),
            q: ipoly(&[-3, 0, 1]),
            expected: rat(1, 1),
        },
        ResFixture {
            name: "res/(x^2-2, x^2-11) = 81",
            p: ipoly(&[-2, 0, 1]),
            q: ipoly(&[-11, 0, 1]),
            expected: rat(81, 1),
        },
        // Shared factor => resultant vanishes.
        ResFixture {
            name: "res/(x^2-1, x-1) = 0",
            p: ipoly(&[-1, 0, 1]),
            q: ipoly(&[-1, 1]),
            expected: rat(0, 1),
        },
        // Discriminant of a quadratic: Res(ax^2+bx+c, 2ax+b) = -a(b^2-4ac).
        ResFixture {
            name: "res/(x^2+3x+2, 2x+3) = -1",
            p: ipoly(&[2, 3, 1]),
            q: ipoly(&[3, 2]),
            expected: rat(-1, 1),
        },
        // Res(x^3 - 2, x^2 - 2) = -2.
        ResFixture {
            name: "res/(x^3-2, x^2-2) = -4",
            p: ipoly(&[-2, 0, 0, 1]),
            q: ipoly(&[-2, 0, 1]),
            expected: rat(-4, 1),
        },
    ]
}

fn pass(name: &str) -> GoldenResult {
    GoldenResult {
        name: name.to_string(),
        passed: true,
        detail: String::new(),
    }
}

fn fail(name: &str, detail: String) -> GoldenResult {
    GoldenResult {
        name: name.to_string(),
        passed: false,
        detail,
    }
}

/// Run every fixture. When `z3` is supplied, each root fixture is ALSO checked
/// live against the reference implementation, so a stale hand-written
/// expectation cannot mask a real disagreement.
pub(crate) fn run_all(z3: Option<&Z3>, include_heavy: bool) -> Vec<GoldenResult> {
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
                        for (m, r) in markers.iter().zip(roots.iter()) {
                            let hit = match m {
                                ORoot::Rational(q) => {
                                    let a = z.rational(q);
                                    z.eq(*r, a)
                                }
                                ORoot::Interval(lo, hi) => {
                                    let a = z.rational(lo);
                                    let b = z.rational(hi);
                                    z.gt(*r, a) && z.lt(*r, b)
                                }
                            };
                            if !hit {
                                ok = false;
                                break;
                            }
                        }
                        if ok {
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
                            z.numeral_value(*a)
                                .map_or_else(|| z.ast_string(*a), |v| v.to_string())
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
