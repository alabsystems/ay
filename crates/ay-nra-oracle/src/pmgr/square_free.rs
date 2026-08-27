// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sparse-polynomial square-free checks.

use super::*;

// ---------------------------------------------------------------------------
// 4. Square-free
// ---------------------------------------------------------------------------

/// `square_free_in(p, x)` preserves the exact real root set of every
/// specialization, and divides `p`.
pub(crate) fn check_pm_square_free(z3: &Z3, g: &GenPm, sab: Sabotage) -> Outcome {
    let mut m = OPolyMgr::new();
    let s = m.mk(&g.s_terms);
    let other = m.mk(&g.a_terms);
    if m.is_zero(&s) || m.is_zero(&other) {
        return Outcome::Skipped("degenerate factor");
    }
    // p = s^2 * other, so there is always a square to remove.
    let s2 = m.mul(&s, &s);
    let p = m.mul(&s2, &other);
    if m.is_zero(&p) {
        return Outcome::Skipped("degenerate product");
    }
    let Some(mut sf) = m.square_free_in(&p, X) else {
        return Outcome::Declined("square_free_in refused");
    };
    if sab.on() {
        let f = saboteur(&mut m);
        sf = m.mul(&sf, &f);
    }
    let mut comparisons = 0u64;

    // (a) The square-free part divides the input.
    comparisons += 1;
    if !m.divides(&sf, &p) {
        return Divergence::outcome(
            "pm-square-free",
            "identity",
            "the square-free part does not divide p".to_string(),
            vec![
                ("p".to_string(), render(&m, &p)),
                ("sf".to_string(), render(&m, &sf)),
            ],
        );
    }

    // (b) The z3 leg: identical real root sets after specialization.
    let (Some(pb), Some(sb)) = (
        m.specialize(&p, X, &g.point),
        m.specialize(&sf, X, &g.point),
    ) else {
        return Outcome::Skipped("specialization left a variable standing");
    };
    if pb.is_empty() || sb.is_empty() {
        return Outcome::Skipped("a specialization vanished");
    }
    let (Some(pr), Some(sr)) = (z3.roots(&to_rationals(&pb)), z3.roots(&to_rationals(&sb))) else {
        return Outcome::Skipped("z3 declined a specialization");
    };
    comparisons += 1;
    if pr.len() != sr.len() {
        return Divergence::outcome(
            "pm-square-free",
            "z3",
            format!(
                "root counts differ: p has {} distinct real roots, its square-free part has {}",
                pr.len(),
                sr.len()
            ),
            vec![
                ("p".to_string(), render(&m, &p)),
                ("sf".to_string(), render(&m, &sf)),
                ("p_bar".to_string(), render_dense(&pb)),
                ("sf_bar".to_string(), render_dense(&sb)),
            ],
        );
    }
    for (i, (a, b)) in pr.iter().zip(sr.iter()).enumerate() {
        comparisons += 1;
        let Some(equal) = z3.eq(*a, *b) else {
            return Outcome::Skipped("z3 errored while comparing roots");
        };
        if !equal {
            return Divergence::outcome(
                "pm-square-free",
                "z3",
                format!("root #{i} of p and of its square-free part differ"),
                vec![
                    ("p".to_string(), render(&m, &p)),
                    ("sf".to_string(), render(&m, &sf)),
                    ("p_bar".to_string(), render_dense(&pb)),
                    ("sf_bar".to_string(), render_dense(&sb)),
                ],
            );
        }
    }
    Outcome::Match(comparisons)
}

/// `square_free(p)` — the WHOLE-POLYNOMIAL entry point, which recurses through
/// the content instead of working in one variable.
///
/// This check exists because a verifier proved the entry point was invisible.
/// Every other `pm` check calls `square_free_in`; nothing called `square_free`,
/// and dropping its integer content — returning `(x-1)` for `square_free(6(x-1)^2)`
/// instead of `6(x-1)` — produced ZERO divergences over 4,000 cases and still
/// passed the unit test named for that exact behaviour, because that test used
/// an all-±1 input where the dropped factor is 1.
///
/// The reason the obvious legs cannot see it is worth stating: an integer scalar
/// divides, preserves every real root, and preserves square-freeness. Root-set
/// equality — the strongest leg the `square_free_in` check has — is blind to it
/// by construction. What pins it is Gauss's lemma:
///
/// `square_free(p) = i * square_free(c) * sqfpart_x(pp)` where `i` is the integer
/// content of `p` and both `c` and `pp` are integer-primitive; exact division
/// preserves primitivity, so the two right-hand factors contribute content `1` and
///
/// > `int_content(square_free(p)) == int_content(p)`  exactly.
///
/// That identity is leg (b), and it is the leg that catches the defect.
pub(crate) fn check_pm_square_free_all(z3: &Z3, g: &GenPm, sab: Sabotage) -> Outcome {
    let mut manager = OPolyMgr::new();
    let planted_square = manager.mk(&g.s_terms);
    let other = manager.mk(&g.a_terms);
    if manager.is_zero(&planted_square) || manager.is_zero(&other) {
        return Outcome::Skipped("degenerate factor");
    }
    let scale = 2 + g.point.first().map_or(0, |(_, value)| {
        (value.magnitude() % 5u32)
            .to_string()
            .parse::<i64>()
            .unwrap_or(0)
    });
    let base = manager.mul(&planted_square, &planted_square);
    let base = manager.mul(&base, &other);
    let polynomial = manager.mul_int(&base, &BigInt::from(scale));
    if manager.is_zero(&polynomial) {
        return Outcome::Skipped("degenerate product");
    }
    let Some(mut square_free) = manager.square_free(&polynomial) else {
        return Outcome::Declined("square_free refused");
    };
    if sab.on() {
        let factor = saboteur(&mut manager);
        square_free = manager.mul(&square_free, &factor);
    }
    let case = SquareFreeCase {
        polynomial: &polynomial,
        planted_square: &planted_square,
        square_free: &square_free,
    };
    let mut comparisons = 0;
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_square_free_properties(&mut manager, sab, &case),
    ) {
        return outcome;
    }
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_power_containment(&mut manager, &case),
    ) {
        return outcome;
    }
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_square_free_roots(z3, g, &mut manager, &case),
    ) {
        return outcome;
    }
    Outcome::Match(comparisons)
}

struct SquareFreeCase<'a> {
    polynomial: &'a OMgrPoly,
    planted_square: &'a OMgrPoly,
    square_free: &'a OMgrPoly,
}

fn square_free_inputs(manager: &OPolyMgr, case: &SquareFreeCase<'_>) -> Vec<(String, String)> {
    vec![
        ("p".to_string(), render(manager, case.polynomial)),
        ("sf".to_string(), render(manager, case.square_free)),
    ]
}

fn check_square_free_properties(
    manager: &mut OPolyMgr,
    sab: Sabotage,
    case: &SquareFreeCase<'_>,
) -> Outcome {
    if !manager.divides(case.square_free, case.polynomial) {
        return Divergence::outcome(
            "pm-square-free-all",
            "identity",
            "whole-polynomial square-free part does not divide p".to_string(),
            square_free_inputs(manager, case),
        );
    }
    let input_content = manager.int_content(case.polynomial);
    let answer_content = manager.int_content(case.square_free);
    if input_content != answer_content {
        return Divergence::outcome(
            "pm-square-free-all",
            "identity",
            format!(
                "integer content changed: p has {input_content}, square-free part {answer_content}"
            ),
            square_free_inputs(manager, case),
        );
    }
    let mut comparisons = 2;
    if !sab.on() {
        let Some(again) = manager.square_free(case.square_free) else {
            return Outcome::Declined("square_free refused its own output");
        };
        comparisons += 1;
        if again != *case.square_free {
            return Divergence::outcome(
                "pm-square-free-all",
                "identity",
                "square_free is not idempotent".to_string(),
                square_free_inputs(manager, case),
            );
        }
    }
    if !manager.is_const(case.planted_square) {
        comparisons += 1;
        if manager.total_degree(case.square_free) >= manager.total_degree(case.polynomial) {
            return Divergence::outcome(
                "pm-square-free-all",
                "identity",
                format!(
                    "planted square did not lower degree ({} vs {})",
                    manager.total_degree(case.square_free),
                    manager.total_degree(case.polynomial)
                ),
                square_free_inputs(manager, case),
            );
        }
    }
    Outcome::Match(comparisons)
}

fn check_power_containment(manager: &mut OPolyMgr, case: &SquareFreeCase<'_>) -> Outcome {
    let total_degree = manager.total_degree(case.polynomial) as usize;
    let max_power = total_degree.min(6);
    if max_power < 1 || manager.len(case.square_free) > 40 {
        return Outcome::Match(0);
    }
    let mut comparisons = 0;
    let mut divides = false;
    for exponent in 1..=max_power {
        let power = manager.pow(case.square_free, u32::try_from(exponent).unwrap_or(1));
        comparisons += 1;
        if manager.divides(case.polynomial, &power) {
            divides = true;
            break;
        }
    }
    if !divides && max_power == total_degree {
        return Divergence::outcome(
            "pm-square-free-all",
            "identity",
            format!("p divides no sf^k for k <= {max_power}; a factor was lost"),
            square_free_inputs(manager, case),
        );
    }
    Outcome::Match(comparisons)
}

fn check_square_free_roots(
    z3: &Z3,
    g: &GenPm,
    manager: &mut OPolyMgr,
    case: &SquareFreeCase<'_>,
) -> Outcome {
    let (Some(input), Some(answer)) = (
        manager.specialize(case.polynomial, X, &g.point),
        manager.specialize(case.square_free, X, &g.point),
    ) else {
        return Outcome::Skipped("specialization left a variable standing");
    };
    if input.is_empty() || answer.is_empty() {
        return Outcome::Skipped("a specialization vanished");
    }
    let (Some(input_roots), Some(answer_roots)) = (
        z3.roots(&to_rationals(&input)),
        z3.roots(&to_rationals(&answer)),
    ) else {
        return Outcome::Skipped("z3 declined a specialization");
    };
    if input_roots.len() != answer_roots.len() {
        return Divergence::outcome(
            "pm-square-free-all",
            "z3",
            format!(
                "root counts differ: p has {}, square-free part {}",
                input_roots.len(),
                answer_roots.len()
            ),
            specialized_square_free_inputs(manager, case, &input, &answer),
        );
    }
    let mut comparisons = 1;
    for (index, (a, b)) in input_roots.iter().zip(&answer_roots).enumerate() {
        comparisons += 1;
        let Some(equal) = z3.eq(*a, *b) else {
            return Outcome::Skipped("z3 errored while comparing roots");
        };
        if !equal {
            return Divergence::outcome(
                "pm-square-free-all",
                "z3",
                format!("root #{index} of p and square-free part differ"),
                specialized_square_free_inputs(manager, case, &input, &answer),
            );
        }
    }
    Outcome::Match(comparisons)
}

fn specialized_square_free_inputs(
    manager: &OPolyMgr,
    case: &SquareFreeCase<'_>,
    input: &[BigInt],
    answer: &[BigInt],
) -> Vec<(String, String)> {
    let mut details = square_free_inputs(manager, case);
    details.push(("p_bar".to_string(), render_dense(input)));
    details.push(("sf_bar".to_string(), render_dense(answer)));
    details
}
