// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn solve_text(text: &str) -> SolveOutcome {
    let instance = parse::parse_instance(text).expect("parses");
    solve_instance(&instance, &SolveOptions::default())
}

/// `solve_text` with definability elimination admitted on projected inputs.
fn solve_text_projected_elimination(text: &str) -> SolveOutcome {
    let instance = parse::parse_instance(text).expect("parses");
    solve_instance(
        &instance,
        &SolveOptions {
            projected_definability_elimination: true,
            ..SolveOptions::default()
        },
    )
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
fn invalid_public_instance_fields_fail_closed_before_solving() {
    let mut instance = parse::parse_instance("p cnf 1 0\n").expect("parses");
    instance.clauses.push(vec![0]);

    let outcome = solve_instance(&instance, &SolveOptions::default());

    assert_eq!(outcome.satisfiable, None);
    assert_eq!(outcome.value, None);
    assert!(outcome
        .warnings
        .iter()
        .any(|warning| warning.contains("format error: clause 1: clause literal 0")));
}

#[test]
fn contradictory_projection_track_state_fails_closed_before_solving() {
    let base = parse::parse_instance("p cnf 2 0\n").expect("parses");
    let mut mc = base.clone();
    mc.show = Some(vec![1]);
    let mut wmc = base;
    wmc.ptype = ProblemType::Wmc;
    wmc.show = Some(vec![1]);

    for (label, instance, expected_warning) in [
        ("mc", mc, "mc instances cannot contain a projection set"),
        ("wmc", wmc, "wmc instances cannot contain a projection set"),
    ] {
        let outcome = solve_instance(&instance, &SolveOptions::default());

        assert_eq!(outcome.satisfiable, None, "{label}");
        assert_eq!(outcome.value, None, "{label}");
        assert!(
            outcome
                .warnings
                .iter()
                .any(|warning| warning.contains(expected_warning)),
            "{label}: {:?}",
            outcome.warnings
        );
    }
}

#[test]
fn projected_tracks_without_show_records_count_the_empty_projection() {
    for (problem_type, expected) in [
        ("pmc", ExactValue::Nat(num_bigint::BigUint::from(1u32))),
        ("pwmc", ExactValue::Rat(BigRational::from_integer(1.into()))),
    ] {
        let instance =
            parse::parse_instance(&format!("c t {problem_type}\np cnf 2 0\n")).expect("parses");
        assert_eq!(instance.show, Some(Vec::new()), "{problem_type}");

        let outcome = solve_instance(&instance, &SolveOptions::default());

        assert_eq!(outcome.satisfiable, Some(true), "{problem_type}");
        assert_eq!(outcome.value, Some(expected), "{problem_type}");
    }
}

#[test]
fn manually_projected_complex_track_fails_closed_before_solving() {
    let mut instance = parse::parse_instance("c t amc-complex\np cnf 1 0\n").expect("parses");
    instance.show = Some(vec![1]);

    let outcome = solve_instance(&instance, &SolveOptions::default());

    assert_eq!(outcome.satisfiable, None);
    assert_eq!(outcome.value, None);
    assert!(outcome.warnings.iter().any(|warning| {
        warning.contains("amc-complex instances cannot contain a projection set")
    }));
}

#[test]
fn conflicting_weight_declarations_fail_closed_end_to_end() {
    let instance = parse::parse_instance(
        "c t wmc\np cnf 1 0\nc p weight 1 1 0\nc p weight 1 2 0\nc p weight -1 1 0\n",
    )
    .expect("individual declarations parse");

    let outcome = solve_instance(&instance, &SolveOptions::default());

    assert_eq!(outcome.satisfiable, None);
    assert_eq!(outcome.value, None);
    assert!(outcome
        .warnings
        .iter()
        .any(|warning| warning.contains("conflicting duplicate weight for literal 1")));
}

#[test]
fn malformed_weights_fail_closed_before_unsat_shortcut() {
    for (label, text, expected_warning) in [
        (
            "real",
            "c t wmc\np cnf 1 2\nc p weight 1 2 0\n1 0\n-1 0\n",
            "requires the complement weight",
        ),
        (
            "complex",
            "c t amc-complex\np cnf 1 2\nc p weight 1 1+0i 0\n1 0\n-1 0\n",
            "only one polarity",
        ),
    ] {
        let instance = parse::parse_instance(text).expect("declarations parse individually");
        let outcome = solve_instance(&instance, &SolveOptions::default());

        assert_eq!(outcome.satisfiable, None, "{label}");
        assert_eq!(outcome.value, None, "{label}");
        assert!(
            outcome
                .warnings
                .iter()
                .any(|warning| warning.contains(expected_warning)),
            "{label}: {:?}",
            outcome.warnings
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

/// Clauses of `gates` OR gates over `inputs` input variables, shaped like
/// MC 2026 `2B_033`: gate variable `inputs + g + 1` is the OR of four
/// distinct inputs chosen by a fixed pseudo-random sequence.
fn or_gate_clauses(inputs: usize, gates: usize) -> Vec<Vec<i32>> {
    let mut state = 0x2b03_3u64;
    let mut clauses = Vec::new();
    for g in 0..gates {
        let out = (inputs + g + 1) as i32;
        let mut chosen: Vec<i32> = Vec::new();
        while chosen.len() < 4 {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            let input = 1 + (state % inputs as u64) as i32;
            if !chosen.contains(&input) {
                chosen.push(input);
            }
        }
        for &input in &chosen {
            clauses.push(vec![-input, out]);
        }
        let mut long = vec![-out];
        long.extend(&chosen);
        clauses.push(long);
    }
    clauses
}

fn instance_text(
    ptype: &str,
    num_vars: usize,
    clauses: &[Vec<i32>],
    weight_lines: &[String],
    show: Option<&[u32]>,
) -> String {
    let mut text = format!("p cnf {num_vars} {}\nc t {ptype}\n", clauses.len());
    if let Some(show) = show {
        text.push_str("c p show");
        for v in show {
            text.push_str(&format!(" {v}"));
        }
        text.push_str(" 0\n");
    }
    for line in weight_lines {
        text.push_str(line);
        text.push('\n');
    }
    for clause in clauses {
        for l in clause {
            text.push_str(&format!("{l} "));
        }
        text.push_str("0\n");
    }
    text
}

fn reports_definability_elimination(outcome: &SolveOutcome) -> bool {
    outcome
        .warnings
        .iter()
        .any(|warning| warning.starts_with("definability elimination:"))
}

/// AY-OTHER-3: weighted inputs, unweighted OR gates. Every gate is defined by
/// the inputs and weighs 1 on both literals, so eliminating the gates keeps
/// the weighted count, which is the product of `w(i) + w(-i)` over the inputs
/// (the gates are otherwise unconstrained).
#[test]
fn weighted_or_gates_are_eliminated_and_the_count_stays_exact() {
    use num_traits::One;
    let (inputs, gates) = (100, 100);
    let clauses = or_gate_clauses(inputs, gates);
    let pairs = [("1/20", "19/20"), ("3/5", "1/5"), ("0", "2"), ("-1/3", "4")];
    let mut weight_lines = Vec::new();
    let mut expected = BigRational::one();
    for input in 1..=inputs {
        let (positive, negative) = pairs[input % pairs.len()];
        weight_lines.push(format!("c p weight {input} {positive} 0"));
        weight_lines.push(format!("c p weight -{input} {negative} 0"));
        expected *=
            parse::parse_rational(positive).unwrap() + parse::parse_rational(negative).unwrap();
    }

    let wmc = instance_text("wmc", inputs + gates, &clauses, &weight_lines, None);
    let outcome = solve_text(&wmc);
    assert!(
        reports_definability_elimination(&outcome),
        "{:?}",
        outcome.warnings
    );
    assert_eq!(outcome.satisfiable, Some(true));
    assert_eq!(outcome.value, Some(ExactValue::Rat(expected.clone())));

    // pwmc projected on the inputs: the gates lie outside the projection set.
    // By default G stays off on projected inputs (speed not yet measured);
    // with the option it removes the gates. The count is the same either way.
    let show: Vec<u32> = (1..=inputs as u32).collect();
    let pwmc = instance_text(
        "pwmc",
        inputs + gates,
        &clauses,
        &weight_lines,
        Some(show.as_slice()),
    );
    let outcome = solve_text_projected_elimination(&pwmc);
    assert!(
        reports_definability_elimination(&outcome),
        "{:?}",
        outcome.warnings
    );
    assert_eq!(outcome.value, Some(ExactValue::Rat(expected)));

    // Without the option G stays off on projected input, and the count must
    // be the same. That run searches over the gates, so this control uses a
    // small instance: at a hundred gates it is the search the option exists
    // to avoid, and it does not end (the first run of this test, at full
    // size, was stopped after 18 minutes and 5 GB).
    let (inputs, gates) = (6, 6);
    let clauses = or_gate_clauses(inputs, gates);
    let mut weight_lines = Vec::new();
    let mut expected = BigRational::one();
    for input in 1..=inputs {
        let (positive, negative) = pairs[input % pairs.len()];
        weight_lines.push(format!("c p weight {input} {positive} 0"));
        weight_lines.push(format!("c p weight -{input} {negative} 0"));
        expected *=
            parse::parse_rational(positive).unwrap() + parse::parse_rational(negative).unwrap();
    }
    let show: Vec<u32> = (1..=inputs as u32).collect();
    let pwmc = instance_text(
        "pwmc",
        inputs + gates,
        &clauses,
        &weight_lines,
        Some(show.as_slice()),
    );
    let outcome = solve_text_projected_elimination(&pwmc);
    assert_eq!(outcome.value, Some(ExactValue::Rat(expected.clone())));
    let outcome = solve_text(&pwmc);
    assert!(
        !reports_definability_elimination(&outcome),
        "{:?}",
        outcome.warnings
    );
    assert_eq!(outcome.value, Some(ExactValue::Rat(expected)));
}

/// Builds the instance, resolves its weights as `solve_instance` does, and
/// returns `eliminable_variables`.
fn eliminable_for(text: &str, projected_elimination: bool) -> EliminableVariables {
    let instance = parse::parse_instance(text).expect("parses");
    let mut warnings = Vec::new();
    let weights = prepare_weights(&instance, &mut warnings).expect("weights resolve");
    eliminable_variables(&instance, &weights, projected_elimination)
}

/// The admission rule of weighted definability elimination (AY-OTHER-3),
/// checked on the real function: per track, real and complex weights, equal
/// and unequal pairs, 0/0, undeclared and (pwmc) unshown weights, with and
/// without a show set, with the projected option off and on.
#[test]
fn eliminable_variables_admits_exactly_equal_weight_pairs_outside_the_show_set() {
    use super::EliminableVariables::{All, Off, Only};
    let clause = "1 2 3 4 5 0\n";
    // mc: everything; pmc with a show set: off by default, else the unshown.
    assert_eq!(
        eliminable_for(&format!("p cnf 5 1\nc t mc\n{clause}"), false),
        All
    );
    assert_eq!(
        eliminable_for(&format!("p cnf 5 1\nc t mc\n{clause}"), true),
        All
    );
    let pmc = format!("p cnf 5 1\nc t pmc\nc p show 1 3 0\n{clause}");
    assert_eq!(eliminable_for(&pmc, false), Off);
    assert_eq!(
        eliminable_for(&pmc, true),
        Only(vec![false, true, false, true, true])
    );
    // pmc whose show set names every variable is not projected.
    let pmc_all = format!("p cnf 5 1\nc t pmc\nc p show 1 2 3 4 5 0\n{clause}");
    assert_eq!(eliminable_for(&pmc_all, false), All);

    // wmc: 1 equal 1/2-1/2, 2 unequal 3/5-1/5, 3 undeclared (1-1),
    // 4 is 0/0, 5 unequal 0-2.
    let real_weights = "c p weight 1 1/2 0\nc p weight -1 1/2 0\n\
                        c p weight 2 3/5 0\nc p weight -2 1/5 0\n\
                        c p weight 4 0 0\nc p weight -4 0 0\n\
                        c p weight 5 0 0\nc p weight -5 2 0\n";
    let wmc = format!("p cnf 5 1\nc t wmc\n{real_weights}{clause}");
    let expected_wmc = Only(vec![true, false, true, true, false]);
    assert_eq!(eliminable_for(&wmc, false), expected_wmc);
    assert_eq!(eliminable_for(&wmc, true), expected_wmc);

    // pwmc showing 1 and 2: off by default; with the option only the
    // unshown 3, 4, 5 (their declared weights are ignored, so they resolve
    // to 1-1 and are admitted even where the declaration was unequal).
    let pwmc = format!("p cnf 5 1\nc t pwmc\nc p show 1 2 0\n{real_weights}{clause}");
    assert_eq!(eliminable_for(&pwmc, false), Off);
    assert_eq!(
        eliminable_for(&pwmc, true),
        Only(vec![false, false, true, true, true])
    );
    // pwmc showing every variable is not projected: the equal-pair rule.
    let pwmc_all = format!("p cnf 5 1\nc t pwmc\nc p show 1 2 3 4 5 0\n{real_weights}{clause}");
    assert_eq!(eliminable_for(&pwmc_all, false), expected_wmc);

    // amc-complex: 1 equal 0.5+0.5i, 2 conjugates (same real part),
    // 3 undeclared (1+0i), 4 is 0/0, 5 is 2i against 2, 6 is 1 against 1+0i.
    let complex = "p cnf 6 1\nc t amc-complex\n\
                   c p weight 1 0.5+0.5i 0\nc p weight -1 0.5+0.5i 0\n\
                   c p weight 2 0.5+0.5i 0\nc p weight -2 0.5-0.5i 0\n\
                   c p weight 4 0 0\nc p weight -4 0 0\n\
                   c p weight 5 0+2i 0\nc p weight -5 2 0\n\
                   c p weight 6 1 0\nc p weight -6 1+0i 0\n\
                   1 2 3 4 5 6 0\n";
    assert_eq!(
        eliminable_for(complex, false),
        Only(vec![true, false, true, true, false, true])
    );
}

/// The complex track: inputs with complex weights, gates with the default
/// `1+0i`. Expected: the product of `w(i) + w(-i)` over the inputs.
#[test]
fn complex_weighted_or_gates_are_eliminated_and_the_count_stays_exact() {
    use num_traits::{One, Zero};
    let (inputs, gates) = (100, 100);
    let clauses = or_gate_clauses(inputs, gates);
    let mut weight_lines = Vec::new();
    let (mut re, mut im) = (BigRational::one(), BigRational::zero());
    for input in 1..=inputs {
        let (positive, negative, sum) = if input % 2 == 0 {
            ("0.4+0.2i", "0.6+0.6i", ("1", "0.8"))
        } else {
            ("0.5+0.5i", "0.5", ("1", "0.5"))
        };
        weight_lines.push(format!("c p weight {input} {positive} 0"));
        weight_lines.push(format!("c p weight -{input} {negative} 0"));
        let (sum_re, sum_im) = (
            parse::parse_rational(sum.0).unwrap(),
            parse::parse_rational(sum.1).unwrap(),
        );
        let new_re = &re * &sum_re - &im * &sum_im;
        let new_im = &re * &sum_im + &im * &sum_re;
        re = new_re;
        im = new_im;
    }
    let text = instance_text("amc-complex", inputs + gates, &clauses, &weight_lines, None);
    let outcome = solve_text(&text);
    assert!(
        reports_definability_elimination(&outcome),
        "{:?}",
        outcome.warnings
    );
    assert_eq!(outcome.value, Some(ExactValue::Complex(re, im)));
}

/// End to end against brute force: a small random formula with planted
/// gates and random weights (1, equal pairs, pairs not summing to 1, zero,
/// negative), beside a 120-variable implication cycle of weight-1 variables
/// (two models) that lifts the residual over preprocessing's 100-variable
/// floor. Expected count: 2 times the brute-force count of the small part.
/// Projected trials run with and without the projected option (same count).
/// Eliminations are counted inside the small weighted part only (the cycle
/// would satisfy a whole-formula check by itself), by running the same
/// preprocessing with the same admission mask.
#[test]
fn weighted_and_projected_counts_match_brute_force_after_preprocessing() {
    use num_traits::Zero;
    let mut state = 0x0a40_7e33u64;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let pairs = [
        ("1", "1"),
        ("1", "1"),
        ("1/2", "1/2"),
        ("3/5", "1/5"),
        ("1/20", "19/20"),
        ("0", "2"),
        ("-1/3", "4"),
    ];
    let mut small_part_eliminations = [0usize; 2];
    for trial in 0..24 {
        let small = 6 + (next() % 3) as usize;
        let mut clauses: Vec<Vec<i32>> = Vec::new();
        // Gates small-1 and small are defined from earlier variables.
        for out in [small as i32 - 1, small as i32] {
            let a = 1 + (next() % 3) as i32;
            let b = 4;
            match next() % 3 {
                0 => {
                    clauses.push(vec![-out, a]);
                    clauses.push(vec![-out, b]);
                    clauses.push(vec![out, -a, -b]);
                }
                1 => {
                    clauses.push(vec![out, -a]);
                    clauses.push(vec![out, -b]);
                    clauses.push(vec![-out, a, b]);
                }
                _ => {
                    clauses.push(vec![-out, a, b]);
                    clauses.push(vec![-out, -a, -b]);
                    clauses.push(vec![out, -a, b]);
                    clauses.push(vec![out, a, -b]);
                }
            }
        }
        for _ in 0..next() % 3 {
            let v = 1 + (next() % small as u64) as i32;
            let w = 1 + (next() % small as u64) as i32;
            clauses.push(vec![if next() % 2 == 0 { v } else { -v }, w]);
        }
        let weights: Vec<(&str, &str)> = (0..small)
            .map(|_| pairs[(next() % pairs.len() as u64) as usize])
            .collect();
        let small_clauses = clauses.clone();
        let cycle = 120;
        for i in 0..cycle {
            let a = (small + 1 + i) as i32;
            let b = (small + 1 + (i + 1) % cycle) as i32;
            clauses.push(vec![-a, b]);
        }
        let num_vars = small + cycle;
        let mut weight_lines = Vec::new();
        for (v, (positive, negative)) in weights.iter().enumerate() {
            weight_lines.push(format!("c p weight {} {positive} 0", v + 1));
            weight_lines.push(format!("c p weight -{} {negative} 0", v + 1));
        }
        let projected = trial % 2 == 1;
        let small_show: Vec<bool> = (0..small).map(|_| !projected || next() % 2 == 0).collect();
        let show: Vec<u32> = (1..=num_vars as u32)
            .filter(|&v| v as usize > small || small_show[v as usize - 1])
            .collect();
        let text = if projected {
            instance_text(
                "pwmc",
                num_vars,
                &clauses,
                &weight_lines,
                Some(show.as_slice()),
            )
        } else {
            instance_text("wmc", num_vars, &clauses, &weight_lines, None)
        };
        let outcome = solve_text_projected_elimination(&text);
        // Brute force over the small part (weights of unshown variables
        // are ignored, as in pwmc), times the cycle's two models.
        let shown_weights: Vec<(&str, &str)> = weights
            .iter()
            .zip(&small_show)
            .map(|(&pair, &shown)| if shown { pair } else { ("1", "1") })
            .collect();
        let mut expected = BigRational::zero();
        let mut projections = std::collections::BTreeSet::new();
        for m in 0..(1u64 << small) {
            let satisfied = small_clauses.iter().all(|clause| {
                clause.iter().any(|&l| {
                    let bit = (m >> (l.unsigned_abs() - 1)) & 1 == 1;
                    if l > 0 {
                        bit
                    } else {
                        !bit
                    }
                })
            });
            if satisfied {
                let key: u64 = (0..small)
                    .filter(|&v| small_show[v] && (m >> v) & 1 == 1)
                    .fold(0u64, |bits, v| bits | (1u64 << v));
                projections.insert(key);
            }
        }
        for key in projections {
            let mut product = BigRational::from_integer(2.into());
            for (v, (positive, negative)) in shown_weights.iter().enumerate() {
                if small_show[v] {
                    let w = if (key >> v) & 1 == 1 {
                        positive
                    } else {
                        negative
                    };
                    product *= parse::parse_rational(w).unwrap();
                }
            }
            expected += product;
        }
        assert_eq!(
            outcome.value,
            Some(ExactValue::Rat(expected.clone())),
            "trial {trial}: {text}\nwarnings {:?}",
            outcome.warnings
        );
        if projected {
            let default_outcome = solve_text(&text);
            assert!(
                !reports_definability_elimination(&default_outcome),
                "trial {trial}: projected elimination ran without the option"
            );
            assert_eq!(
                default_outcome.value,
                Some(ExactValue::Rat(expected)),
                "trial {trial} (default options): {text}"
            );
        }
        // Eliminations inside the small part, whose weights are not all 1.
        let instance = parse::parse_instance(&text).expect("parses");
        let mut prep_warnings = Vec::new();
        let prepared = prepare_weights(&instance, &mut prep_warnings).expect("weights resolve");
        let eliminable = eliminable_variables(&instance, &prepared, true);
        let prepped = prep::preprocess(
            instance.num_vars,
            &instance.clauses,
            prep::PrepOptions {
                elimination: eliminable.as_elimination(),
            },
        );
        let weighted = shown_weights
            .iter()
            .any(|(positive, negative)| positive != negative);
        if weighted {
            small_part_eliminations[usize::from(projected)] += prepped
                .pinned_defined
                .iter()
                .filter(|literal| literal.unsigned_abs() as usize <= small)
                .count();
        }
    }
    assert!(
        small_part_eliminations[0] > 0,
        "no unprojected trial eliminated a variable of the weighted small part"
    );
    assert!(
        small_part_eliminations[1] > 0,
        "no projected trial eliminated a variable of the weighted small part"
    );
}
