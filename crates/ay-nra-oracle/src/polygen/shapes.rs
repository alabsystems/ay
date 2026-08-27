// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Adversarial polynomial-shape construction.

use super::*;

pub(super) fn build(rng: &mut Rng, shape: Shape, max_degree: usize) -> Vec<BigRational> {
    match shape {
        Shape::AlgebraicSmall => build_algebraic_small(rng, max_degree),
        Shape::Zero => Vec::new(),
        Shape::Constant => build_constant(rng),
        Shape::Dense | Shape::Sparse | Shape::HugeCoeffs => {
            build_dense_like(rng, shape, max_degree)
        }
        Shape::LinearProduct | Shape::RepeatedRoots => build_linear_product(rng, shape, max_degree),
        Shape::PerfectSquare => build_perfect_square(rng, max_degree),
        Shape::TimesDerivative => build_times_derivative(rng, max_degree),
        Shape::NearDegenerateLead => build_near_degenerate_lead(rng, max_degree),
        Shape::TinyLead => build_tiny_lead(rng, max_degree),
        Shape::ClusteredRational => build_clustered_rational(rng, max_degree),
        Shape::PureRoot => build_pure_root(rng, max_degree),
        Shape::Wilkinson => build_wilkinson(rng, max_degree),
    }
}

fn build_algebraic_small(rng: &mut Rng, max_degree: usize) -> Vec<BigRational> {
    let upper = i64::try_from(max_degree.max(2)).unwrap_or(2);
    let degree = usize::try_from(rng.range(2, upper)).unwrap_or(2);
    let mut coefficients = (0..=degree)
        .map(|_| rng.rational_of_class(1))
        .collect::<Vec<_>>();
    if coefficients[degree].is_zero() {
        coefficients[degree] = BigRational::one();
    }
    coefficients
}

fn build_constant(rng: &mut Rng) -> Vec<BigRational> {
    let class = u8::try_from(rng.below(5)).unwrap_or(0);
    let constant = rng.rational_of_class(class);
    if constant.is_zero() {
        vec![BigRational::one()]
    } else {
        vec![constant]
    }
}

fn build_dense_like(rng: &mut Rng, shape: Shape, max_degree: usize) -> Vec<BigRational> {
    let class = if shape == Shape::HugeCoeffs {
        4
    } else {
        u8::try_from(rng.below(5)).unwrap_or(0)
    };
    let cap = if class >= 4 {
        max_degree.min(4)
    } else {
        max_degree
    };
    let degree = usize::try_from(rng.below(u64::try_from(cap).unwrap_or(1) + 1)).unwrap_or(1);
    let sparse = shape == Shape::Sparse;
    let mut coefficients = (0..=degree)
        .map(|_| {
            if sparse && rng.chance(3, 5) {
                BigRational::zero()
            } else {
                rng.rational_of_class(class)
            }
        })
        .collect::<Vec<_>>();
    if coefficients[degree].is_zero() {
        coefficients[degree] = BigRational::one();
    }
    coefficients
}

fn build_linear_product(rng: &mut Rng, shape: Shape, max_degree: usize) -> Vec<BigRational> {
    let max_factors = max_degree.clamp(1, 10);
    let count =
        usize::try_from(rng.below(u64::try_from(max_factors).unwrap_or(1))).unwrap_or(0) + 1;
    let mut product = vec![BigRational::one()];
    let mut degree = 0;
    for _ in 0..count {
        let leading = BigRational::from_integer(BigInt::from(rng.range(1, 9)));
        let constant = BigRational::from_integer(BigInt::from(rng.range(-9, 9)));
        let linear = vec![constant, leading];
        let multiplicity = if shape == Shape::RepeatedRoots {
            usize::try_from(rng.range(1, 3)).unwrap_or(1)
        } else {
            1
        };
        for _ in 0..multiplicity {
            if degree + 1 > max_degree {
                break;
            }
            product = mul(&product, &linear);
            degree += 1;
        }
    }
    product
}

fn build_perfect_square(rng: &mut Rng, max_degree: usize) -> Vec<BigRational> {
    let half = max_degree / 2;
    let degree = usize::try_from(rng.below(u64::try_from(half).unwrap_or(0) + 1)).unwrap_or(0) + 1;
    let class = u8::try_from(rng.below(3)).unwrap_or(0);
    let mut base = (0..=degree)
        .map(|_| rng.rational_of_class(class))
        .collect::<Vec<_>>();
    if base[degree].is_zero() {
        base[degree] = BigRational::one();
    }
    mul(&base, &base)
}

fn build_times_derivative(rng: &mut Rng, max_degree: usize) -> Vec<BigRational> {
    let half = max_degree / 2;
    let degree = usize::try_from(rng.below(u64::try_from(half).unwrap_or(0) + 1)).unwrap_or(0) + 2;
    let class = u8::try_from(rng.below(3)).unwrap_or(0);
    let mut base = (0..=degree)
        .map(|_| rng.rational_of_class(class))
        .collect::<Vec<_>>();
    if base[degree].is_zero() {
        base[degree] = BigRational::one();
    }
    let derivative = derivative(&base);
    if derivative.is_empty() {
        base
    } else {
        mul(&base, &derivative)
    }
}

fn extreme_degree(rng: &mut Rng, max_degree: usize) -> usize {
    usize::try_from(rng.below(u64::try_from(max_degree.min(5)).unwrap_or(1))).unwrap_or(0) + 1
}

fn build_near_degenerate_lead(rng: &mut Rng, max_degree: usize) -> Vec<BigRational> {
    let degree = extreme_degree(rng, max_degree);
    let mut coefficients = (0..degree)
        .map(|_| rng.rational_of_class(4))
        .collect::<Vec<_>>();
    let one = BigRational::one();
    coefficients.push(if rng.chance(1, 2) { one.clone() } else { -one });
    coefficients
}

fn build_tiny_lead(rng: &mut Rng, max_degree: usize) -> Vec<BigRational> {
    let degree = extreme_degree(rng, max_degree);
    let mut coefficients = (0..degree)
        .map(|_| rng.rational_of_class(2))
        .collect::<Vec<_>>();
    let exponent = u32::try_from(rng.range(3, 12)).unwrap_or(3);
    let tiny = BigRational::new(BigInt::one(), BigInt::from(10u32).pow(exponent));
    coefficients.push(if rng.chance(1, 2) {
        tiny.clone()
    } else {
        -tiny
    });
    coefficients
}

fn build_clustered_rational(rng: &mut Rng, max_degree: usize) -> Vec<BigRational> {
    let exponent = u32::try_from(rng.range(2, 6)).unwrap_or(4);
    let scale = BigInt::from(10u32).pow(exponent);
    let base = rng.range(1, 99);
    let count = usize::try_from(rng.range(1, 3))
        .unwrap_or(1)
        .min(max_degree.max(1));
    let mut product = vec![BigRational::one()];
    for index in 0..count {
        let factor = vec![
            BigRational::from_integer(-BigInt::from(base + i64::try_from(index).unwrap_or(0))),
            BigRational::from_integer(scale.clone()),
        ];
        product = mul(&product, &factor);
    }
    product
}

fn build_pure_root(rng: &mut Rng, max_degree: usize) -> Vec<BigRational> {
    let degree =
        usize::try_from(rng.range(2, i64::try_from(max_degree.max(2)).unwrap_or(2))).unwrap_or(2);
    let class = u8::try_from(rng.below(4)).unwrap_or(0);
    let mut coefficients = vec![BigRational::zero(); degree + 1];
    coefficients[0] = -rng.rational_of_class(class);
    coefficients[degree] = BigRational::one();
    coefficients
}

fn build_wilkinson(rng: &mut Rng, max_degree: usize) -> Vec<BigRational> {
    let degree =
        usize::try_from(rng.range(2, i64::try_from(max_degree.max(2)).unwrap_or(2))).unwrap_or(2);
    let mut product = vec![BigRational::one()];
    for root in 1..=degree {
        product = mul(
            &product,
            &[
                BigRational::from_integer(-BigInt::from(root)),
                BigRational::one(),
            ],
        );
    }
    product
}
