// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Included by the parent module to keep fixture order explicit.

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
    let mut fixtures = primary_root_fixtures(&x5_minus_x_minus_1, &x5_plus_x_minus_1);
    fixtures.extend(heavy_root_fixtures(&x5_minus_x_minus_1, &x5_plus_x_minus_1));
    fixtures.extend(algebraic_root_fixtures());
    fixtures
}

fn primary_root_fixtures(
    x5_minus_x_minus_1: &[BigRational],
    x5_plus_x_minus_1: &[BigRational],
) -> Vec<RootFixture> {
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
            coeffs: x5_minus_x_minus_1.to_vec(),
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
                x5_minus_x_minus_1.to_vec(),
                x5_plus_x_minus_1.to_vec(),
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
    ]
}

fn heavy_root_fixtures(
    x5_minus_x_minus_1: &[BigRational],
    x5_plus_x_minus_1: &[BigRational],
) -> Vec<RootFixture> {
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
            name: "upoly/((x^5-x-1)(x^5+x-1)(1000x-1167))^2",
            coeffs: pow_coeffs(
                &product(&[
                    x5_minus_x_minus_1.to_vec(),
                    x5_plus_x_minus_1.to_vec(),
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
                pow_coeffs(x5_minus_x_minus_1, 2),
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
    ]
}

fn algebraic_root_fixtures() -> Vec<RootFixture> {
    vec![
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
