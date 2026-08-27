// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integer-polynomial square-free decomposition checks.

use super::*;

// ---------------------------------------------------------------------------
// Check 2: Yun's square-free decomposition over Z
// ---------------------------------------------------------------------------

/// Yun's decomposition `f == c * prod f_i^i`.
///
/// Three statements:
///
///   (a) the EXACT identity — `c * prod f_i^i` reproduces the input coefficient
///       for coefficient. This is the statement that a "square-free part"
///       cannot make: `p / gcd(p, p')` throws the multiplicities away, and
///       AY's existing `univariate::square_free_part` returns exactly that.
///   (b) each `f_i` is square-free (`gcd(f_i, f_i') `is constant) and the `f_i`
///       are pairwise coprime.
///   (c) **z3-backed**: `prod f_i` (the radical) has the same real ROOT SET as
///       the input, compared root by root with `Z3_algebraic_eq`. The integer
///       content is a unit for this leg, so (a) is what pins it — the lesson
///       the `pm-square-free-all` defect taught.
pub(crate) fn check_sqf_decomp(z3: &Z3, g: &GenUp, sab: Sabotage) -> Outcome {
    let input = build_z(g);
    if input.is_zero() || input.degree() == Some(0) {
        return Outcome::Skipped("degenerate input");
    }
    let Some((content, mut factors)) = input.square_free_decomposition() else {
        return Outcome::Declined("square_free_decomposition refused");
    };
    if sab.on() {
        if let Some(slot) = factors
            .iter_mut()
            .find(|(_, multiplicity)| *multiplicity > 1)
        {
            slot.1 -= 1;
        } else if let Some((factor, _)) = factors.first().cloned() {
            factors.push((factor, 1));
        } else {
            return Outcome::Skipped("nothing to sabotage");
        }
    }
    let mut product = OUniZ::from_coeffs(vec![content.clone()]);
    let mut radical = OUniZ::from_coeffs(vec![BigInt::one()]);
    for (factor, multiplicity) in &factors {
        radical = radical.mul(factor);
        for _ in 0..*multiplicity {
            product = product.mul(factor);
        }
    }
    if product != input {
        return Divergence::outcome(
            "up-z-sqf-decomp",
            "identity",
            "c * prod f_i^i != input".to_string(),
            vec![
                ("f".to_string(), render_z(&input)),
                ("c".to_string(), content.to_string()),
                ("factors".to_string(), render_factors(&factors)),
                ("product".to_string(), render_z(&product)),
            ],
        );
    }
    let mut comparisons = 1;
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_square_free_factors(&input, &factors),
    ) {
        return outcome;
    }
    if let Err(outcome) = add_matches(&mut comparisons, check_radical_roots(z3, &input, &radical)) {
        return outcome;
    }
    Outcome::Match(comparisons)
}

fn render_factors(factors: &[(OUniZ, usize)]) -> String {
    factors
        .iter()
        .map(|(factor, multiplicity)| format!("({})^{multiplicity}", render_z(factor)))
        .collect::<Vec<_>>()
        .join(" * ")
}

fn check_square_free_factors(input: &OUniZ, factors: &[(OUniZ, usize)]) -> Outcome {
    let mut comparisons = 0;
    for (factor, multiplicity) in factors {
        comparisons += 1;
        let Some(gcd) = factor.gcd(&factor.derivative()) else {
            return Outcome::Declined("gcd refused");
        };
        if gcd.degree() != Some(0) {
            return Divergence::outcome(
                "up-z-sqf-decomp",
                "identity",
                format!("factor with multiplicity {multiplicity} is not square-free"),
                vec![
                    ("f".to_string(), render_z(input)),
                    ("factor".to_string(), render_z(factor)),
                    ("gcd(fac,fac')".to_string(), render_z(&gcd)),
                ],
            );
        }
    }
    for first in 0..factors.len() {
        for second in first + 1..factors.len() {
            comparisons += 1;
            let Some(gcd) = factors[first].0.gcd(&factors[second].0) else {
                return Outcome::Declined("gcd refused");
            };
            if gcd.degree() != Some(0) {
                return Divergence::outcome(
                    "up-z-sqf-decomp",
                    "identity",
                    format!("factors {first} and {second} share a non-trivial gcd"),
                    vec![
                        ("f".to_string(), render_z(input)),
                        ("f_i".to_string(), render_z(&factors[first].0)),
                        ("f_j".to_string(), render_z(&factors[second].0)),
                        ("gcd".to_string(), render_z(&gcd)),
                    ],
                );
            }
        }
    }
    Outcome::Match(comparisons)
}

fn check_radical_roots(z3: &Z3, input: &OUniZ, radical: &OUniZ) -> Outcome {
    let (Some(input_roots), Some(radical_roots)) = (
        z3.roots(&to_rationals(input)),
        z3.roots(&to_rationals(radical)),
    ) else {
        return Outcome::Skipped("z3 declined");
    };
    if input_roots.len() != radical_roots.len() {
        return Divergence::outcome(
            "up-z-sqf-decomp",
            "z3",
            format!(
                "root counts differ: input has {}, radical has {}",
                input_roots.len(),
                radical_roots.len()
            ),
            vec![
                ("f".to_string(), render_z(input)),
                ("radical".to_string(), render_z(radical)),
            ],
        );
    }
    let mut comparisons = 1;
    for (index, (input_root, radical_root)) in input_roots.iter().zip(&radical_roots).enumerate() {
        comparisons += 1;
        let Some(equal) = z3.eq(*input_root, *radical_root) else {
            return Outcome::Skipped("z3 errored while comparing roots");
        };
        if !equal {
            return Divergence::outcome(
                "up-z-sqf-decomp",
                "z3",
                format!("root #{index} of input and radical differ"),
                vec![
                    ("f".to_string(), render_z(input)),
                    ("radical".to_string(), render_z(radical)),
                ],
            );
        }
    }
    Outcome::Match(comparisons)
}
