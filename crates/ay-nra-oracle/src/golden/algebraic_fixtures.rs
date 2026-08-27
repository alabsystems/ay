// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Included by the parent module to keep fixture order explicit.

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
