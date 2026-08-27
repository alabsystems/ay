// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Included by the binary root; the harness remains a single private namespace.

/// Adversarial generator: shapes chosen to break projection/decomposition
/// reasoning — shared roots, zero discriminant (repeated roots), strict vs
/// non-strict boundaries, high degree, near-tangency, and plain random.
fn gen_primary_shape(rng: &mut Rng, shape: &str) -> Option<GeneratedShape> {
    let generated = match shape {
        // Coefficient vector padded with high-order ZEROS: the true degree is
        // lower than `p.len()-1`, which is where a leading-coefficient
        // assumption goes wrong.
        "padded" => {
            let a = rng.range(-4, 4);
            let mut p = pmul(&ints(&[-a, 1]), &ints(&[-(a + 2), 1]));
            for _ in 0..=rng.below(3) {
                p.push(BigInt::zero());
            }
            let mut q = ints(&[-rng.range(-4, 4), 1]);
            q.push(BigInt::zero());
            q.push(BigInt::zero());
            (
                vec![p, q],
                vec![CONDS[rng.below(6) as usize], CONDS[rng.below(6) as usize]],
            )
        }
        // A large integer CONTENT factor: same roots, different primitive part.
        "content" => {
            let c = 6 + rng.range(0, 30);
            let a = rng.range(-4, 4);
            let p: Vec<BigInt> = pmul(&ints(&[-a, 1]), &ints(&[-(a + 1), 1]))
                .iter()
                .map(|t| t * BigInt::from(c))
                .collect();
            let q: Vec<BigInt> = ints(&[-rng.range(-6, 6), 2])
                .iter()
                .map(|t| t * BigInt::from(c))
                .collect();
            (
                vec![p, q],
                vec![CONDS[rng.below(6) as usize], CONDS[rng.below(6) as usize]],
            )
        }
        // Degree up to 8, with repeated factors so discriminants vanish.
        "deg8" => {
            let mut p = ints(&[1]);
            for _ in 0..(6 + rng.below(3)) {
                p = pmul(&p, &ints(&[-rng.range(-3, 3), 1]));
            }
            let mut q = ints(&[1]);
            for _ in 0..(2 + rng.below(3)) {
                q = pmul(&q, &ints(&[-rng.range(-3, 3), 1]));
            }
            (
                vec![p, q],
                vec![CONDS[rng.below(6) as usize], CONDS[rng.below(6) as usize]],
            )
        }
        // Rational and irrational roots interleaved and CLOSE together.
        "mixed-rat-irrat" => {
            let ds = [2i64, 3, 5, 6, 7, 8, 10, 11];
            let d = ds[rng.below(8) as usize];
            let p = ints(&[-d, 0, 1]);
            let a = rng.range(-3, 3);
            let q = pmul(&ints(&[-a, 1]), &ints(&[-(a + 1), 1]));
            let r = ints(&[-(d * 4 + 1), 0, 4]);
            (
                vec![p, q, r],
                vec![
                    CONDS[rng.below(6) as usize],
                    CONDS[rng.below(6) as usize],
                    CONDS[rng.below(6) as usize],
                ],
            )
        }
        "shared-root" => {
            // p and q share the root a; strictness decides.
            let a = rng.range(-4, 4);
            let b = rng.range(-4, 4);
            let c = rng.range(-4, 4);
            let p = pmul(&ints(&[-a, 1]), &ints(&[-b, 1]));
            let q = pmul(&ints(&[-a, 1]), &ints(&[-c, 1]));
            (
                vec![p, q],
                vec![CONDS[rng.below(6) as usize], CONDS[rng.below(6) as usize]],
            )
        }
        "repeated-root" => {
            // (x-a)^2 : discriminant zero. Sign never changes at a.
            let a = rng.range(-4, 4);
            let f = ints(&[-a, 1]);
            let p = pmul(&f, &f);
            let b = rng.range(-4, 4);
            (
                vec![p, ints(&[-b, 1])],
                vec![CONDS[rng.below(6) as usize], CONDS[rng.below(6) as usize]],
            )
        }
        _ => return None,
    };
    Some(generated)
}

fn gen_boundary_shape(rng: &mut Rng, shape: &str) -> Option<GeneratedShape> {
    let generated = match shape {
        "boundary-strict" => {
            // x >= a and x <= a : satisfiable only AT a. Flip strictness by draw.
            let a = rng.range(-4, 4);
            let c0 = if rng.below(2) == 0 {
                OISignCond::Ge
            } else {
                OISignCond::Gt
            };
            let c1 = if rng.below(2) == 0 {
                OISignCond::Le
            } else {
                OISignCond::Lt
            };
            (vec![ints(&[-a, 1]), ints(&[-a, 1])], vec![c0, c1])
        }
        "tangent" => {
            // x^2 - 2a x + a^2 + t : touches zero when t = 0, no real root t>0.
            let a = rng.range(-3, 3);
            let t = rng.range(0, 2);
            let p = ints(&[a * a + t, -2 * a, 1]);
            (
                vec![p, ints(&[-rng.range(-4, 4), 1])],
                vec![CONDS[rng.below(6) as usize], CONDS[rng.below(6) as usize]],
            )
        }
        "high-degree" => {
            let mut p = ints(&[1]);
            let n = 3 + rng.below(3);
            for _ in 0..n {
                p = pmul(&p, &ints(&[-rng.range(-3, 3), 1]));
            }
            let mut q = ints(&[1]);
            for _ in 0..n {
                q = pmul(&q, &ints(&[-rng.range(-3, 3), 1]));
            }
            (
                vec![p, q],
                vec![CONDS[rng.below(6) as usize], CONDS[rng.below(6) as usize]],
            )
        }
        "many-lits" => {
            let n = 4 + rng.below(5);
            let mut ps = Vec::new();
            let mut cs = Vec::new();
            for _ in 0..n {
                let d = 1 + rng.below(2);
                let mut p = ints(&[1]);
                for _ in 0..d {
                    p = pmul(&p, &ints(&[-rng.range(-4, 4), 1]));
                }
                ps.push(p);
                cs.push(CONDS[rng.below(6) as usize]);
            }
            (ps, cs)
        }
        _ => return None,
    };
    Some(generated)
}

fn gen_remaining_shape(rng: &mut Rng, shape: &str) -> GeneratedShape {
    match shape {
        "irrational-tight" => {
            // x^2 - d < 0 with x^2 - e > 0 : conflict iff d <= e. Also nested.
            let ds = [2i64, 3, 5, 6, 7, 10, 11, 13];
            let d = ds[rng.below(8) as usize];
            let e = ds[rng.below(8) as usize];
            (
                vec![ints(&[-d, 0, 1]), ints(&[-e, 0, 1])],
                vec![CONDS[rng.below(6) as usize], CONDS[rng.below(6) as usize]],
            )
        }
        "eq-chain" => {
            let a = rng.range(-4, 4);
            let b = rng.range(-4, 4);
            (
                vec![
                    ints(&[-a, 1]),
                    ints(&[-b, 1]),
                    ints(&[-rng.range(-4, 4), 0, 1]),
                ],
                vec![OISignCond::Eq, OISignCond::Eq, CONDS[rng.below(6) as usize]],
            )
        }
        "ne-cover" => {
            // != on a poly whose roots are all of the other's feasible points.
            let a = rng.range(-3, 3);
            let p = pmul(&ints(&[-a, 1]), &ints(&[-(a + 1), 1]));
            (
                vec![p.clone(), p],
                vec![OISignCond::Ne, CONDS[rng.below(6) as usize]],
            )
        }
        "random-deg3" | "random-deg4" => {
            let d = if shape == "random-deg3" { 3 } else { 4 };
            let n = 2 + rng.below(2);
            let mut ps = Vec::new();
            let mut cs = Vec::new();
            for _ in 0..n {
                let mut c: Vec<BigInt> = (0..=d).map(|_| BigInt::from(rng.range(-5, 5))).collect();
                if c[d].is_zero() {
                    c[d] = BigInt::one();
                }
                ps.push(c);
                cs.push(CONDS[rng.below(6) as usize]);
            }
            (ps, cs)
        }
        _ => {
            let n = 3 + rng.below(6);
            let mut ps = Vec::new();
            let mut cs = Vec::new();
            for _ in 0..n {
                let a = rng.range(-8, 8);
                let m = rng.range(1, 3);
                ps.push(ints(&[-a, m]));
                cs.push(CONDS[rng.below(6) as usize]);
            }
            (ps, cs)
        }
    }
}

fn draw_shape(rng: &mut Rng) -> &'static str {
    match rng.below(16) {
        12 => "padded",
        13 => "content",
        14 => "deg8",
        15 => "mixed-rat-irrat",
        0 => "shared-root",
        1 => "repeated-root",
        2 => "boundary-strict",
        3 => "tangent",
        4 => "high-degree",
        5 => "many-lits",
        6 => "irrational-tight",
        7 => "eq-chain",
        8 => "ne-cover",
        9 => "random-deg3",
        10 => "random-deg4",
        _ => "linear-many",
    }
}

fn gencase(rng: &mut Rng) -> Case {
    let shape = draw_shape(rng);
    let (polys, conds) = gen_primary_shape(rng, shape)
        .or_else(|| gen_boundary_shape(rng, shape))
        .unwrap_or_else(|| gen_remaining_shape(rng, shape));
    Case {
        polys,
        conds,
        shape,
    }
}
