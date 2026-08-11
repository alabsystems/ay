// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn solve_text(text: &str) -> SolveOutcome {
    let instance = parse::parse_instance(text).expect("parses");
    solve_instance(&instance, &SolveOptions::default())
}

#[test]
fn invalid_numeric_options_fail_closed_without_panicking() {
    let instance = parse::parse_instance("p cnf 1 1\nc t mc\n1 0\n").expect("parses");
    for (field, options) in [
        (
            "phase1_secs",
            SolveOptions {
                phase1_secs: f64::INFINITY,
                ..SolveOptions::default()
            },
        ),
        (
            "td_budget_secs",
            SolveOptions {
                td_budget_secs: -1.0,
                ..SolveOptions::default()
            },
        ),
        (
            "decow",
            SolveOptions {
                decow: f64::NAN,
                ..SolveOptions::default()
            },
        ),
    ] {
        let outcome = solve_instance(&instance, &options);
        assert_eq!(outcome.satisfiable, None, "field {field}");
        assert_eq!(outcome.value, None, "field {field}");
        assert!(
            outcome
                .warnings
                .iter()
                .any(|warning| warning.contains(field)),
            "missing warning for {field}"
        );
    }
}

#[test]
fn end_to_end_spec_example_1() {
    let text = "p cnf 6 4\nc t mc\n-1 -2\n0\n2 3 -4 0\n4 5 0\n4 6 0\n";
    let outcome = solve_text(text);
    assert_eq!(outcome.satisfiable, Some(true));
    assert_eq!(
        outcome.value,
        Some(ExactValue::Nat(num_bigint::BigUint::from(22u32)))
    );
    assert!(output::render(&outcome).contains("c s exact arb int 22"));
}

#[test]
fn end_to_end_spec_example_2_weighted() {
    let text = "p cnf 6 4\nc t wmc\n\
        c p weight 1 0.4 0\nc p weight 2 0.5 0\nc p weight 3 0.4 0\n\
        c p weight 4 0.3 0\nc p weight 5 0.5 0\nc p weight 6 0.7 0\n\
        -1 -2 0\n2 3 -4 0\n4 5 0\n4 6 0\n";
    let outcome = solve_text(text);
    assert_eq!(outcome.satisfiable, Some(true));
    let clauses = vec![vec![-1, -2], vec![2, 3, -4], vec![4, 5], vec![4, 6]];
    let expected = brute_force_weighted(
        6,
        &clauses,
        &[
            ("0.4", "0.6"),
            ("0.5", "0.5"),
            ("0.4", "0.6"),
            ("0.3", "0.7"),
            ("0.5", "0.5"),
            ("0.7", "0.3"),
        ],
    );
    match &outcome.value {
        Some(ExactValue::Rat(r)) => assert_eq!(*r, expected, "weighted count mismatch: {r}"),
        other => panic!("expected rational, got {other:?}"),
    }
}

fn brute_force_weighted(
    num_vars: usize,
    clauses: &[Vec<i32>],
    weights: &[(&str, &str)],
) -> BigRational {
    use num_traits::{One, Zero};
    let w: Vec<(BigRational, BigRational)> = weights
        .iter()
        .map(|(p, n)| {
            (
                parse::parse_rational(p).unwrap(),
                parse::parse_rational(n).unwrap(),
            )
        })
        .collect();
    let mut total = BigRational::zero();
    for m in 0..(1u64 << num_vars) {
        let sat = clauses.iter().all(|cl| {
            cl.iter().any(|&l| {
                let v = l.unsigned_abs() as usize - 1;
                let bit = (m >> v) & 1 == 1;
                if l > 0 {
                    bit
                } else {
                    !bit
                }
            })
        });
        if !sat {
            continue;
        }
        let mut prod = BigRational::one();
        for v in 0..num_vars {
            let bit = (m >> v) & 1 == 1;
            prod *= if bit { &w[v].0 } else { &w[v].1 };
        }
        total += prod;
    }
    total
}

#[test]
fn end_to_end_spec_example_4_projected() {
    let text = "p cnf 6 4 2\nc t pmc\nc p show 1 2 0\n-1 -2 0\n2 3 -4 0\n4 5 0\n4 6 0\n";
    let outcome = solve_text(text);
    assert_eq!(outcome.satisfiable, Some(true));
    assert_eq!(
        outcome.value,
        Some(ExactValue::Nat(num_bigint::BigUint::from(3u32)))
    );
}

#[test]
fn end_to_end_spec_example_5_complex() {
    let text = "p cnf 3 2\nc t amc-complex\n\
        c p weight 1 0.4+0.2i 0\nc p weight -1 0.6+0.6i 0\n\
        c p weight 2 0.5+0.5i 0\nc p weight -2 0.5+0.5i 0\n\
        c p weight 3 0.3+0.7i 0\nc p weight -3 0.7+0.3i 0\n\
        1 -2 0\n-1 3 0\n";
    let outcome = solve_text(text);
    assert_eq!(outcome.satisfiable, Some(true));
    let (re, im) = brute_force_complex(
        3,
        &[vec![1, -2], vec![-1, 3]],
        &[
            ("0.4", "0.2"),
            ("0.6", "0.6"),
            ("0.5", "0.5"),
            ("0.5", "0.5"),
            ("0.3", "0.7"),
            ("0.7", "0.3"),
        ],
    );
    match &outcome.value {
        Some(ExactValue::Complex(gre, gim)) => {
            assert_eq!(*gre, re);
            assert_eq!(*gim, im);
        }
        other => panic!("expected complex, got {other:?}"),
    }
}

fn brute_force_complex(
    num_vars: usize,
    clauses: &[Vec<i32>],
    weights: &[(&str, &str)],
) -> (BigRational, BigRational) {
    use num_traits::{One, Zero};
    let w: Vec<(BigRational, BigRational)> = weights
        .iter()
        .map(|(re, im)| {
            (
                parse::parse_rational(re).unwrap(),
                parse::parse_rational(im).unwrap(),
            )
        })
        .collect();
    let mut total_re = BigRational::zero();
    let mut total_im = BigRational::zero();
    for m in 0..(1u64 << num_vars) {
        let sat = clauses.iter().all(|cl| {
            cl.iter().any(|&l| {
                let v = l.unsigned_abs() as usize - 1;
                let bit = (m >> v) & 1 == 1;
                if l > 0 {
                    bit
                } else {
                    !bit
                }
            })
        });
        if !sat {
            continue;
        }
        let mut prod_re = BigRational::one();
        let mut prod_im = BigRational::zero();
        for v in 0..num_vars {
            let bit = (m >> v) & 1 == 1;
            let (wre, wim) = &w[v * 2 + usize::from(!bit)];
            let new_re = &prod_re * wre - &prod_im * wim;
            let new_im = &prod_re * wim + &prod_im * wre;
            prod_re = new_re;
            prod_im = new_im;
        }
        total_re += prod_re;
        total_im += prod_im;
    }
    (total_re, total_im)
}

#[test]
fn unsat_instance_reports_unsatisfiable() {
    let outcome = solve_text("p cnf 1 2\nc t mc\n1 0\n-1 0\n");
    assert_eq!(outcome.satisfiable, Some(false));
    assert_eq!(
        outcome.value,
        Some(ExactValue::Nat(num_bigint::BigUint::from(0u32)))
    );
}

#[test]
fn pmc_with_no_show_line_is_sat_decision() {
    let outcome = solve_text("p cnf 2 1\nc t pmc\nc p show 0\n1 2 0\n");
    assert_eq!(outcome.satisfiable, Some(true));
    assert_eq!(
        outcome.value,
        Some(ExactValue::Nat(num_bigint::BigUint::from(1u32)))
    );
}
