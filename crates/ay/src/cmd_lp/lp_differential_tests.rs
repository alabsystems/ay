// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Randomised differential test of `ay lp solve` on small CPLEX LP files
//! (AY-N12), in the style of [`super::differential_tests`].
//!
//! Each file is generated together with the model it means, computed here,
//! independently of ay's reader: objective constants, summed repeated terms,
//! every comparator spelling, bounds in every accepted form (`free`,
//! infinity spellings and `1e30`, fixing, reversed and double forms,
//! negative upper bounds after a lower bound), `General` and `Binary`, both
//! senses. Numbers include integers above 2^53 and decimals that are not
//! binary fractions. The exact brute force of the MPS test gives the answer,
//! which the route must not contradict (same rules as there).

use std::io::Write as _;
use std::time::Duration;

use ay_lp::{parse_lp_exact, ExactColumn, ExactProblem, ExactRow, Sense, VarKind};
use num_rational::BigRational;
use num_traits::{Signed, Zero};

use super::differential_tests::{
    brute_force, last_point, q, rational_text, witness, Answer, Lcg, COEFFS, SPLITS,
};
use super::run_solve;

/// `+ c name` / `- c name` for coefficient text `c`.
fn signed_term(coefficient: &str, name: &str) -> String {
    match coefficient.strip_prefix('-') {
        Some(magnitude) => format!(" - {magnitude} {name}"),
        None => format!(" + {coefficient} {name}"),
    }
}

/// Bounds lines of an integer column (`General` unless `binary`), always
/// bounded so that the brute force can enumerate it.
fn integer_bounds(
    rng: &mut Lcg,
    name: &str,
) -> (String, bool, Option<BigRational>, Option<BigRational>) {
    let a = rng.below(5) as i64 - 3;
    let b = a + rng.below(4) as i64;
    let (a_text, b_text) = (a.to_string(), b.to_string());
    let some = |t: &str| Some(q(t));
    match rng.below(7) {
        0 => (String::new(), true, some("0"), some("1")),
        1 => (format!(" 0 <= {name} <= 1\n"), true, some("0"), some("1")),
        2 => (
            format!(" {a_text} <= {name} <= {b_text}\n"),
            false,
            some(&a_text),
            some(&b_text),
        ),
        3 => (
            format!(" {b_text} >= {name} >= {a_text}\n"),
            false,
            some(&a_text),
            some(&b_text),
        ),
        4 => {
            let v = rng.pick(&["9007199254740993", "-9007199254740992", "2", "-1"]);
            (format!(" {name} = {v}\n"), false, some(v), some(v))
        }
        5 => (
            format!(" {name} >= {a_text}\n {name} < {b_text}\n"),
            false,
            some(&a_text),
            some(&b_text),
        ),
        _ => (
            format!(" {name} <= 1.5\n -2.5 =< {name}\n"),
            false,
            some("-2.5"),
            some("1.5"),
        ),
    }
}

fn continuous_bounds(
    rng: &mut Lcg,
    name: &str,
) -> (String, Option<BigRational>, Option<BigRational>) {
    match rng.below(8) {
        0 => (String::new(), Some(q("0")), None),
        1 => (
            format!(" -1.5 <= {name} <= 0.1\n"),
            Some(q("-1.5")),
            Some(q("0.1")),
        ),
        2 => (format!(" -inf <= {name} <= 2.5\n"), None, Some(q("2.5"))),
        3 => (format!(" {name} Free\n"), None, None),
        4 => (format!(" {name} = 0.3\n"), Some(q("0.3")), Some(q("0.3"))),
        // A negative upper bound after a lower bound other than 0.
        5 => (
            format!(" {name} <= -0.5\n {name} >= -2.7\n"),
            Some(q("-2.7")),
            Some(q("-0.5")),
        ),
        6 => (
            format!(" {name} >= -1e30\n {name} <= 0.7\n"),
            None,
            Some(q("0.7")),
        ),
        _ => (
            format!(" {name} >= 0.1\n {name} <= +INFINITY\n"),
            Some(q("0.1")),
            None,
        ),
    }
}

/// One generated file and the model it means.
fn generate(rng: &mut Lcg) -> (String, ExactProblem) {
    let n_int = 1 + rng.below(3);
    let n_cont = rng.below(2);
    let m = 1 + rng.below(3);
    let sense = if rng.chance(50) {
        Sense::Max
    } else {
        Sense::Min
    };
    let mut text = String::from(match sense {
        Sense::Max => "Maximize\n obj:",
        Sense::Min => "Minimize\n obj:",
    });
    let mut columns = Vec::new();
    let mut bounds_text = String::new();
    let (mut general, mut binary) = (String::new(), String::new());
    let mut objective_terms = String::new();
    for j in 0..n_int + n_cont {
        let integral = j < n_int;
        let name = format!("x{j}");
        let objective = rng.pick(&COEFFS);
        objective_terms.push_str(&signed_term(objective, &name));
        let (lines, kind, lower, upper) = if integral {
            let (lines, is_binary, lower, upper) = integer_bounds(rng, &name);
            let list = if is_binary { &mut binary } else { &mut general };
            list.push_str(&format!(" {name}"));
            let kind = if is_binary {
                VarKind::Binary
            } else {
                VarKind::Integer
            };
            (lines, kind, lower, upper)
        } else {
            let (lines, lower, upper) = continuous_bounds(rng, &name);
            (lines, VarKind::Continuous, lower, upper)
        };
        bounds_text.push_str(&lines);
        columns.push(ExactColumn {
            name,
            kind,
            lower,
            upper,
            objective: q(objective),
        });
    }
    let mut offset = BigRational::zero();
    if rng.chance(50) {
        let v = rng.pick(&["-3", "1.5", "0.1", "9007199254740993"]);
        objective_terms.push_str(&signed_term(v, "").trim_end().to_string());
        offset = q(v);
    }
    text.push_str(&objective_terms);
    text.push_str("\nSubject To\n");
    let point: Vec<BigRational> = columns.iter().map(|c| witness(rng, c)).collect();
    let mut rows = Vec::new();
    for r in 0..m {
        let mut sums: Vec<BigRational> = vec![BigRational::zero(); columns.len()];
        let mut lhs = String::new();
        for (j, sum) in sums.iter_mut().enumerate() {
            if !rng.chance(75) && !(j + 1 == columns.len() && lhs.is_empty()) {
                continue;
            }
            let name = format!("x{j}");
            if rng.chance(20) {
                let (a, b) = SPLITS[rng.below(SPLITS.len())];
                lhs.push_str(&signed_term(a, &name));
                lhs.push_str(&signed_term(b, &name));
                *sum = q(a) + q(b);
            } else {
                let a = rng.pick(&COEFFS);
                lhs.push_str(&signed_term(a, &name));
                *sum = q(a);
            }
        }
        let coeffs: Vec<(usize, BigRational)> = sums
            .into_iter()
            .enumerate()
            .filter(|(_, a)| !a.is_zero())
            .collect();
        let activity: BigRational = coeffs.iter().map(|(j, a)| a * &point[*j]).sum();
        let slack = q(rng.pick(&["0", "0", "1", "-1", "0.5"]));
        let kind = rng.below(3);
        let (op, lower, upper) = match kind {
            0 => {
                let rhs = &activity + &slack;
                (rng.pick(&["<=", "=<", "<"]), None, Some(rhs))
            }
            1 => {
                let rhs = &activity - &slack;
                (rng.pick(&[">=", "=>", ">"]), Some(rhs), None)
            }
            _ => {
                let rhs = if rng.chance(70) {
                    activity.clone()
                } else {
                    &activity + &slack
                };
                ("=", Some(rhs.clone()), Some(rhs))
            }
        };
        let rhs = lower.clone().or_else(|| upper.clone()).expect("a side");
        text.push_str(&format!(" R{r}:{lhs} {op} {}\n", rational_text(&rhs)));
        rows.push(ExactRow {
            name: format!("R{r}"),
            coeffs,
            lower,
            upper,
        });
    }
    if !bounds_text.is_empty() {
        text.push_str("Bounds\n");
        text.push_str(&bounds_text);
    }
    if !general.is_empty() {
        text.push_str(&format!("General\n{general}\n"));
    }
    if !binary.is_empty() {
        text.push_str(&format!("Binary\n{binary}\n"));
    }
    text.push_str("End\n");
    let model = ExactProblem {
        name: "obj".into(),
        sense,
        offset,
        columns,
        rows,
    };
    (text, model)
}

/// See the module docs.
#[test]
fn test_route_agrees_with_an_exact_brute_force_on_random_lp() {
    let mut rng = Lcg(0xA1_2026_1119_12);
    let (mut optimal, mut infeasible, mut feasible_only, mut unknown, mut refused) =
        (0, 0, 0, 0, 0);
    let tolerance = ay_lp::exact::write_tolerance();
    for case in 0..200 {
        let (text, model) = generate(&mut rng);
        // A right-hand side of 1e20 or more (a product of two numbers above
        // 2^53) is infinite to some readers: refused.
        let huge = q("1e20");
        if model
            .rows
            .iter()
            .any(|r| r.lower.iter().chain(&r.upper).any(|s| s.abs() >= huge))
        {
            assert!(parse_lp_exact(&text).is_err(), "case {case}\n{text}");
            refused += 1;
            continue;
        }
        // The reader's model is the generated one.
        let read = parse_lp_exact(&text).unwrap_or_else(|e| panic!("case {case}: {e}\n{text}"));
        assert_eq!(
            read, model,
            "case {case}: the reader's model differs\n{text}"
        );
        let answer = brute_force(&model);
        let mut f = tempfile::Builder::new()
            .suffix(".lp")
            .tempfile()
            .expect("tmp");
        f.write_all(text.as_bytes()).expect("write");
        let mut out: Vec<u8> = Vec::new();
        let code = run_solve(f.path(), None, Some(Duration::from_secs(30)), &mut out).expect("run");
        let out = String::from_utf8(out).expect("utf8");
        let status = out
            .lines()
            .rev()
            .find_map(|l| l.strip_prefix("s "))
            .unwrap_or("");
        let context = || format!("case {case}: brute force {answer:?}, exit {code}\n{text}\n{out}");
        let point = last_point(&out, &model);
        if let Some((objective, values)) = &point {
            model
                .check_written(objective, values)
                .unwrap_or_else(|e| panic!("{e}\n{}", context()));
        }
        let written = point.as_ref().map(|(o, _)| q(o));
        match &answer {
            Answer::Infeasible => {
                assert!(point.is_none(), "{}", context());
                assert!(matches!(status, "INFEASIBLE" | "UNKNOWN"), "{}", context());
            }
            Answer::Unbounded => {
                assert!(matches!(status, "FEASIBLE" | "UNKNOWN"), "{}", context());
            }
            Answer::Optimal(v) => {
                assert_ne!(status, "INFEASIBLE", "{}", context());
                if let Some(w) = &written {
                    let gap = match model.sense {
                        Sense::Min => v - w,
                        Sense::Max => w - v,
                    };
                    assert!(
                        gap <= &tolerance * v.abs().max(q("1")),
                        "better than the optimum\n{}",
                        context()
                    );
                }
                if status == "OPTIMAL" {
                    let w = written.clone().expect("a point");
                    assert!(
                        (&w - v).abs() <= &tolerance * v.abs().max(q("1")),
                        "{}",
                        context()
                    );
                }
            }
        }
        match status {
            "OPTIMAL" => optimal += 1,
            "INFEASIBLE" => infeasible += 1,
            "FEASIBLE" => feasible_only += 1,
            _ => unknown += 1,
        }
    }
    eprintln!(
        "route: {optimal} optimal, {infeasible} infeasible, {feasible_only} feasible only, \
         {unknown} unknown; refused (right-hand side 1e20 or more): {refused}"
    );
    assert!(
        optimal >= 50 && infeasible >= 15,
        "too few confirmed verdicts: {optimal} {infeasible}"
    );
}
