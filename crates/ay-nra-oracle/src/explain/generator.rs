// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Included by the parent module so the differential checks share one namespace.

/// Draw a conflict case.
///
/// Six shapes. Roughly half are GUARANTEED conflicts, so the producer has
/// something to produce; the rest are usually SATISFIABLE, which is the
/// direction that matters most — a producer that emits a clause for a
/// satisfiable conjunction is the wrong-`unsat` defect, and it can only be
/// caught on inputs where no clause is due.
///
///   * `opposite`    — one polynomial with `< 0` and `> 0`: always a conflict,
///     and the smallest one, so minimization has an exact expected answer.
///   * `annulus`     — `x^2 - d < 0` with `x^2 - e > 0`. A conflict exactly when
///     `d <= e`, and satisfiable otherwise, from the SAME shape: the generator
///     cannot be accused of only drawing one side.
///   * `algebraic`   — quadratic irrationals with drawn conditions, so the
///     decisive cell boundary is irrational and the rational-only decomposition
///     that a naive checker would build gets the wrong answer.
///   * `linear`      — a chain of linear bounds; conflicting or not by draw.
///   * `at-root`     — conditions that can only be satisfied AT a root
///     (`>= 0` with `<= 0`), so the closed cells decide the case rather than
///     the open ones.
///   * `dense`       — arbitrary low-degree coefficients and arbitrary
///     conditions, mostly satisfiable.
type GeneratedConditions = (Vec<Vec<BigInt>>, Vec<OISignCond>);

fn gen_simple_conditions(
    rng: &mut Rng,
    shape: &str,
    d: i64,
    e: i64,
) -> Option<GeneratedConditions> {
    let generated = match shape {
        "opposite" => {
            let a = rng.range(-5, 5);
            let p = pmul(&ints(&[-a, 1]), &ints(&[-(a + 2), 1]));
            (vec![p.clone(), p], vec![OISignCond::Lt, OISignCond::Gt])
        }
        "annulus" => (
            vec![ints(&[-d, 0, 1]), ints(&[-e, 0, 1])],
            vec![OISignCond::Lt, OISignCond::Gt],
        ),
        "algebraic" => {
            let conds = [
                OISignCond::Lt,
                OISignCond::Le,
                OISignCond::Eq,
                OISignCond::Ne,
                OISignCond::Ge,
                OISignCond::Gt,
            ];
            let c0 = conds[usize::try_from(rng.below(6)).unwrap_or(0)];
            let c1 = conds[usize::try_from(rng.below(6)).unwrap_or(0)];
            let c2 = conds[usize::try_from(rng.below(6)).unwrap_or(0)];
            (
                vec![
                    ints(&[-d, 0, 1]),
                    ints(&[-e, 0, 1]),
                    ints(&[-rng.range(-4, 4), 1]),
                ],
                vec![c0, c1, c2],
            )
        }
        "linear" => {
            let n = 2 + usize::try_from(rng.below(2)).unwrap_or(0);
            let mut ps = Vec::with_capacity(n);
            let mut cs = Vec::with_capacity(n);
            for _ in 0..n {
                ps.push(ints(&[-rng.range(-6, 6), 1]));
                cs.push(if rng.below(2) == 0 {
                    OISignCond::Gt
                } else {
                    OISignCond::Lt
                });
            }
            (ps, cs)
        }
        "at-root" => {
            let p = ints(&[-d, 0, 1]);
            let q = ints(&[-rng.range(-4, 4), 1]);
            (
                vec![p.clone(), p, q],
                vec![
                    OISignCond::Ge,
                    OISignCond::Le,
                    if rng.below(2) == 0 {
                        OISignCond::Ne
                    } else {
                        OISignCond::Eq
                    },
                ],
            )
        }
        _ => return None,
    };
    Some(generated)
}

fn gen_complex_conditions(rng: &mut Rng, shape: &str) -> GeneratedConditions {
    match shape {
        "many-roots" => {
            // MANY MERGED ROOTS, deliberately past the six the other shapes
            // reach.
            //
            // This shape exists because a verifier proved the corpus could not
            // see a real wrong-`unsat`. Every other shape here tops out at 3
            // literals of degree <= 2, so at most SIX distinct merged roots.
            // Injecting "skip every open-cell midpoint once there are more than
            // six roots" — a decomposition that silently loses the gaps between
            // roots, which is the wrong-`unsat` shape — produced ZERO
            // divergences over 9,000 cases across three seeds, with selftest
            // 45/45 and golden 44/44, while being a genuine defect: the
            // verifier's own generator emitted a clause whose citation set z3
            // reports SAT.
            //
            // A product of k distinct linear factors gives exactly k roots, so
            // 4..=9 factors puts the merged count on both sides of that cliff.
            let k = 4 + usize::try_from(rng.below(6)).unwrap_or(0);
            let mut p = ints(&[1]);
            let mut r = -(i64::try_from(k).unwrap_or(4));
            for _ in 0..k {
                p = pmul(&p, &ints(&[-r, 1]));
                r += 1 + i64::from(rng.below(2) as u32);
            }
            // A second literal that bounds the line, so the conjunction can be
            // a genuine conflict rather than trivially satisfiable.
            let hi = ints(&[-(r + 2), 1]);
            (
                vec![p, hi],
                vec![
                    if rng.below(2) == 0 {
                        OISignCond::Gt
                    } else {
                        OISignCond::Lt
                    },
                    OISignCond::Lt,
                ],
            )
        }
        _ => {
            let n = 2 + usize::try_from(rng.below(2)).unwrap_or(0);
            let conds = [
                OISignCond::Lt,
                OISignCond::Le,
                OISignCond::Eq,
                OISignCond::Ne,
                OISignCond::Ge,
                OISignCond::Gt,
            ];
            let mut ps = Vec::with_capacity(n);
            let mut cs = Vec::with_capacity(n);
            for _ in 0..n {
                let deg = 1 + usize::try_from(rng.below(2)).unwrap_or(0);
                let mut c: Vec<BigInt> =
                    (0..=deg).map(|_| BigInt::from(rng.range(-6, 6))).collect();
                if c[deg].is_zero() {
                    c[deg] = BigInt::one();
                }
                ps.push(c);
                cs.push(conds[usize::try_from(rng.below(6)).unwrap_or(0)]);
            }
            (ps, cs)
        }
    }
}

pub(crate) fn gen_ex(rng: &mut Rng) -> GenEx {
    let shape = match rng.below(7) {
        0 => "opposite",
        1 => "annulus",
        2 => "algebraic",
        3 => "linear",
        4 => "at-root",
        5 => "many-roots",
        _ => "dense",
    };
    let d = IRRATIONALS[usize::try_from(rng.below(IRRATIONALS.len() as u64)).unwrap_or(0)];
    let e = IRRATIONALS[usize::try_from(rng.below(IRRATIONALS.len() as u64)).unwrap_or(0)];
    let (polys, conds) = gen_simple_conditions(rng, shape, d, e)
        .unwrap_or_else(|| gen_complex_conditions(rng, shape));

    // Bivariate inputs for the projection check: `x`-coefficients, each a list
    // of `(y-exponent, coefficient)` pairs.
    let bi = vec![
        vec![
            vec![(1u32, -1i64)],
            vec![(0, rng.range(-3, 3))],
            vec![(0, 1)],
        ],
        vec![
            vec![(2u32, 1i64), (0, -(1 + rng.range(0, 5)))],
            vec![],
            vec![(0, 1)],
        ],
    ];

    GenEx {
        polys,
        conds,
        bi,
        shape,
    }
}
