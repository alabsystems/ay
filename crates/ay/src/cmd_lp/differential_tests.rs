// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Randomised differential test of `ay lp solve` on small MPS files (AY-N11,
//! AY-N6 reviews).
//!
//! Each file is generated together with the model it means, computed here,
//! independently of ay's reader: the checker's bound rules entry by entry,
//! RANGES by row type and sign, summed duplicate entries, the objective
//! constant, both objective senses. Numbers include integers above 2^53,
//! decimals that are not binary fractions, and negative bounds. An exact
//! brute force (enumeration of the integer columns, an exact one-variable LP
//! for the continuous column) gives the answer, which the route must not
//! contradict:
//!
//! - an infeasible model: no point, and `s INFEASIBLE` or `s UNKNOWN`;
//! - an optimum `v`: every written point passes the referee's test on the
//!   generated model and is not better than `v`; `s OPTIMAL` only at `v`;
//! - an unbounded model: never `s OPTIMAL` or `s INFEASIBLE`.
//!
//! The dense simplex on the rounded copy is compared too: a point it finds
//! that is exactly feasible is never better than the optimum. Its other
//! disagreements (a false infeasibility, a point that is only feasible
//! after rounding) are counted and reported: they are why its verdicts are
//! not printed for MPS input.
//!
//! When `AY_MIPLIB_SOLCHECKER` names the organizers' `solchecker`, every
//! written point is also checked by it with the competition's tolerances.

use std::io::Write as _;
use std::time::Duration;

use ay_lp::exact::decimal::parse_decimal;
use ay_lp::{parse_mps_exact, ExactColumn, ExactProblem, ExactRow, Sense, VarKind};
use num_rational::BigRational;
use num_traits::{Signed, Zero};

use super::run_solve;

/// A small deterministic generator (64-bit LCG).
pub(super) struct Lcg(pub(super) u64);

impl Lcg {
    pub(super) fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 >> 33
    }

    pub(super) fn below(&mut self, n: usize) -> usize {
        usize::try_from(self.next()).unwrap_or(0) % n
    }

    pub(super) fn pick<'a>(&mut self, items: &[&'a str]) -> &'a str {
        items[self.below(items.len())]
    }

    pub(super) fn chance(&mut self, percent: usize) -> bool {
        self.below(100) < percent
    }
}

pub(super) fn q(text: &str) -> BigRational {
    parse_decimal(text).expect("generator number")
}

/// Coefficients: small integers, decimals that are not binary fractions,
/// integers an `f64` cannot hold (and their exponent spelling).
pub(super) const COEFFS: [&str; 16] = [
    "1",
    "-1",
    "2",
    "-3",
    "0.1",
    "-0.3",
    "2.5",
    "1e-1",
    "3.0e0",
    "-1.25",
    ".5",
    "9007199254740993",
    "-9007199254740992",
    "9.007199254740993e15",
    "4503599627370497",
    "-7",
];
/// Pairs written as two entries of one (column, row): their exact sums are
/// 9007199254740993, 0.3, 0 (the entry vanishes) and 2.
pub(super) const SPLITS: [(&str, &str); 4] = [
    ("9007199254740992", "1"),
    ("0.1", "0.2"),
    ("1", "-1"),
    ("2.5", "-0.5"),
];

/// One generated file and the model it means.
struct Case {
    text: String,
    model: ExactProblem,
    /// The file uses `OBJSENSE MAX` on its header line, which the checker
    /// does not read.
    checker_reads: bool,
}

/// A column's `BOUNDS` lines and the bounds they give, by the checker's
/// rules (computed here, not by ay).
fn integer_bounds(rng: &mut Lcg, name: &str) -> (String, Option<BigRational>, Option<BigRational>) {
    let a = rng.below(5) as i64 - 3;
    let b = a + rng.below(4) as i64;
    let line = |kind: &str, v: &str| format!(" {kind} BND {name} {v}\n");
    match rng.below(8) {
        0 => (String::new(), Some(q("0")), Some(q("1"))),
        1 => (line("UP", "1"), Some(q("0")), Some(q("1"))),
        // LO resets the binary default's upper bound; UP sets it again.
        2 => (
            format!(
                "{}{}",
                line("LO", &a.to_string()),
                line("UP", &b.to_string())
            ),
            Some(q(&a.to_string())),
            Some(q(&b.to_string())),
        ),
        // UP 1 keeps the default; the later LO resets the upper bound.
        3 => (
            format!(
                "{}{}{}",
                line("UP", "1"),
                line("LO", &a.to_string()),
                line("UP", &b.to_string())
            ),
            Some(q(&a.to_string())),
            Some(q(&b.to_string())),
        ),
        4 => {
            let v = rng.pick(&["9007199254740993", "-9007199254740992", "2", "-1"]);
            (line("FX", v), Some(q(v)), Some(q(v)))
        }
        5 => (
            format!(
                " MI BND {name}\n{}{}",
                line("UP", &b.to_string()),
                line("LO", &a.to_string())
            ),
            Some(q(&a.to_string())),
            Some(q(&b.to_string())),
        ),
        6 => (format!(" BV BND {name}\n"), Some(q("0")), Some(q("1"))),
        _ => (
            format!("{}{}", line("LO", "-2.5"), line("UP", "1.5")),
            Some(q("-2.5")),
            Some(q("1.5")),
        ),
    }
}

fn continuous_bounds(
    rng: &mut Lcg,
    name: &str,
) -> (String, Option<BigRational>, Option<BigRational>) {
    let line = |kind: &str, v: &str| format!(" {kind} BND {name} {v}\n");
    match rng.below(7) {
        0 => (String::new(), Some(q("0")), None),
        1 => (
            format!("{}{}", line("LO", "-1.5"), line("UP", "0.1")),
            Some(q("-1.5")),
            Some(q("0.1")),
        ),
        2 => (
            format!(" MI BND {name}\n{}", line("UP", "2.5")),
            None,
            Some(q("2.5")),
        ),
        3 => (format!(" FR BND {name}\n"), None, None),
        4 => (line("FX", "0.3"), Some(q("0.3")), Some(q("0.3"))),
        // A negative UP followed by a lower bound other than 0: accepted.
        5 => (
            format!("{}{}", line("UP", "-0.5"), line("LO", "-2.7")),
            Some(q("-2.7")),
            Some(q("-0.5")),
        ),
        _ => (
            format!("{} PL BND {name}\n", line("LO", "0.1")),
            Some(q("0.1")),
            None,
        ),
    }
}

/// A value inside `[lo, hi]` (an integer for an integer column).
pub(super) fn witness(rng: &mut Lcg, col: &ExactColumn) -> BigRational {
    let lo = col.lower.clone().unwrap_or_else(|| q("-2"));
    let hi = col.upper.clone().unwrap_or_else(|| &lo + q("3"));
    if col.is_integral() {
        let lo = lo.ceil();
        let hi = hi.floor();
        let span = (&hi - &lo).to_integer();
        let steps: usize = if span > num_bigint::BigInt::from(3) {
            3
        } else {
            usize::try_from(span).unwrap_or(0)
        };
        lo + BigRational::from_integer(num_bigint::BigInt::from(rng.below(steps + 1)))
    } else {
        let t = q(rng.pick(&["0", "0.25", "0.5", "1"]));
        &lo + (&hi - &lo) * t
    }
}

fn generate(rng: &mut Lcg) -> Case {
    let n_int = 1 + rng.below(3);
    let n_cont = rng.below(2);
    let m = 1 + rng.below(3);
    let mut text = String::from("NAME RAND\n");
    let sense = if rng.chance(50) {
        Sense::Max
    } else {
        Sense::Min
    };
    let header_form = sense == Sense::Max && rng.chance(50);
    if sense == Sense::Max {
        text.push_str(if header_form {
            "OBJSENSE MAX\n"
        } else {
            "OBJSENSE\n    MAXIMIZE\n"
        });
    }
    let kinds: Vec<&str> = (0..m).map(|_| rng.pick(&["L", "G", "E"])).collect();
    text.push_str("ROWS\n N  OBJ\n");
    for (r, kind) in kinds.iter().enumerate() {
        text.push_str(&format!(" {kind}  R{r}\n"));
    }
    text.push_str("COLUMNS\n");
    let mut columns = Vec::new();
    let mut bounds_text = String::new();
    let mut rows: Vec<Vec<(usize, BigRational)>> = vec![Vec::new(); m];
    for j in 0..n_int + n_cont {
        let integral = j < n_int;
        if j == 0 {
            text.push_str("    MARKER0   'MARKER'   'INTORG'\n");
        }
        if j == n_int {
            text.push_str("    MARKER1   'MARKER'   'INTEND'\n");
        }
        let name = format!("X{j}");
        let objective = rng.pick(&COEFFS);
        text.push_str(&format!("    {name}  OBJ  {objective}\n"));
        for (r, entries) in rows.iter_mut().enumerate() {
            if !rng.chance(75) {
                continue;
            }
            let value = if rng.chance(20) {
                let (a, b) = SPLITS[rng.below(SPLITS.len())];
                text.push_str(&format!("    {name}  R{r}  {a}\n    {name}  R{r}  {b}\n"));
                q(a) + q(b)
            } else {
                let a = rng.pick(&COEFFS);
                text.push_str(&format!("    {name}  R{r}  {a}\n"));
                q(a)
            };
            if !value.is_zero() {
                entries.push((j, value));
            }
        }
        let (lines, lower, upper) = if integral {
            integer_bounds(rng, &name)
        } else {
            continuous_bounds(rng, &name)
        };
        bounds_text.push_str(&lines);
        columns.push(ExactColumn {
            name,
            kind: if integral {
                VarKind::Integer
            } else {
                VarKind::Continuous
            },
            lower,
            upper,
            objective: q(objective),
        });
    }
    if n_cont == 0 {
        text.push_str("    MARKER1   'MARKER'   'INTEND'\n");
    }
    // Right-hand sides around a witness point, so that about half the models
    // are feasible.
    let point: Vec<BigRational> = columns.iter().map(|c| witness(rng, c)).collect();
    text.push_str("RHS\n");
    let mut offset = BigRational::zero();
    if rng.chance(50) {
        let v = rng.pick(&["-3", "1.5", "0.1", "9007199254740993"]);
        text.push_str(&format!("    RHS  OBJ  {v}\n"));
        offset = -q(v);
    }
    let mut sides = Vec::new();
    for (r, entries) in rows.iter().enumerate() {
        let activity: BigRational = entries.iter().map(|(j, a)| a * &point[*j]).sum();
        let slack = q(rng.pick(&["0", "0", "1", "-1", "0.5"]));
        let rhs = match kinds[r] {
            "L" => &activity + &slack,
            "G" => &activity - &slack,
            _ => {
                if rng.chance(70) {
                    activity.clone()
                } else {
                    &activity + &slack
                }
            }
        };
        text.push_str(&format!("    RHS  R{r}  {}\n", rational_text(&rhs)));
        sides.push(rhs);
    }
    let mut ranges = String::new();
    let mut row_sides = Vec::new();
    for (r, b) in sides.iter().enumerate() {
        let range = rng
            .chance(30)
            .then(|| rng.pick(&["2", "-1", "0", "0.5", "-0.25"]));
        if let Some(v) = range {
            ranges.push_str(&format!("    RNG  R{r}  {v}\n"));
        }
        let g = range.map(q);
        let (lower, upper) = match (kinds[r], g) {
            ("L", None) => (None, Some(b.clone())),
            ("G", None) => (Some(b.clone()), None),
            (_, None) => (Some(b.clone()), Some(b.clone())),
            ("L", Some(g)) => (Some(b - g.abs()), Some(b.clone())),
            ("G", Some(g)) => (Some(b.clone()), Some(b + g.abs())),
            (_, Some(g)) if g.is_positive() => (Some(b.clone()), Some(b + g)),
            (_, Some(g)) => (Some(b + g), Some(b.clone())),
        };
        row_sides.push((lower, upper));
    }
    if !ranges.is_empty() {
        text.push_str("RANGES\n");
        text.push_str(&ranges);
    }
    if !bounds_text.is_empty() {
        text.push_str("BOUNDS\n");
        text.push_str(&bounds_text);
    }
    text.push_str("ENDATA\n");
    let rows = rows
        .into_iter()
        .zip(row_sides)
        .enumerate()
        .map(|(r, (coeffs, (lower, upper)))| ExactRow {
            name: format!("R{r}"),
            coeffs,
            lower,
            upper,
        })
        .collect();
    Case {
        text,
        model: ExactProblem {
            name: "RAND".into(),
            sense,
            offset,
            columns,
            rows,
        },
        checker_reads: !header_form,
    }
}

/// The exact decimal text of a terminating rational (every generated side
/// is one), however long.
pub(super) fn rational_text(v: &BigRational) -> String {
    let ten = BigRational::from_integer(10.into());
    let mut scaled = v.clone();
    let mut places = 0usize;
    while !scaled.is_integer() {
        scaled *= &ten;
        places += 1;
        assert!(places < 40, "not a terminating decimal: {v}");
    }
    let digits = scaled.to_integer().abs().to_string();
    let digits = format!("{digits:0>width$}", width = places + 1);
    let (int, frac) = digits.split_at(digits.len() - places);
    let sign = if v.is_negative() { "-" } else { "" };
    let text = if places == 0 {
        format!("{sign}{int}")
    } else {
        format!("{sign}{int}.{frac}")
    };
    assert_eq!(parse_decimal(&text).as_ref(), Some(v));
    text
}

#[derive(Debug, PartialEq)]
pub(super) enum Answer {
    Infeasible,
    Unbounded,
    Optimal(BigRational),
}

/// The exact answer by enumeration of the integer columns and, for the
/// continuous column, an exact one-variable LP.
pub(super) fn brute_force(model: &ExactProblem) -> Answer {
    let ints: Vec<usize> = (0..model.columns.len())
        .filter(|&j| model.columns[j].is_integral())
        .collect();
    let domains: Vec<Vec<BigRational>> = ints
        .iter()
        .map(|&j| {
            let c = &model.columns[j];
            let lo = c.lower.as_ref().expect("bounded").ceil().to_integer();
            let hi = c.upper.as_ref().expect("bounded").floor().to_integer();
            let mut values = Vec::new();
            let mut v = lo;
            while v <= hi {
                values.push(BigRational::from_integer(v.clone()));
                v += 1;
            }
            values
        })
        .collect();
    let cont = (0..model.columns.len()).find(|&j| !model.columns[j].is_integral());
    let better = |a: &BigRational, b: &BigRational| match model.sense {
        Sense::Min => a < b,
        Sense::Max => a > b,
    };
    let mut best: Option<BigRational> = None;
    let mut index = vec![0usize; ints.len()];
    if domains.iter().any(Vec::is_empty) {
        return Answer::Infeasible;
    }
    loop {
        let mut point = vec![BigRational::zero(); model.columns.len()];
        for (k, &j) in ints.iter().enumerate() {
            point[j] = domains[k][index[k]].clone();
        }
        match lp_1d(model, &point, cont) {
            Some(None) => return Answer::Unbounded,
            Some(Some(value)) => {
                if best.as_ref().is_none_or(|b| better(&value, b)) {
                    best = Some(value);
                }
            }
            None => {}
        }
        let mut k = 0;
        loop {
            if k == index.len() {
                return best.map_or(Answer::Infeasible, Answer::Optimal);
            }
            index[k] += 1;
            if index[k] < domains[k].len() {
                break;
            }
            index[k] = 0;
            k += 1;
        }
    }
}

/// With the integer columns of `point` fixed: `None` when infeasible,
/// `Some(None)` when unbounded, else the optimal objective.
fn lp_1d(
    model: &ExactProblem,
    point: &[BigRational],
    cont: Option<usize>,
) -> Option<Option<BigRational>> {
    let mut lo: Option<BigRational> = None;
    let mut hi: Option<BigRational> = None;
    let mut c = BigRational::zero();
    if let Some(y) = cont {
        lo.clone_from(&model.columns[y].lower);
        hi.clone_from(&model.columns[y].upper);
        c = model.columns[y].objective.clone();
    }
    let tighten_lo = |lo: &mut Option<BigRational>, v: BigRational| {
        if lo.as_ref().is_none_or(|l| v > *l) {
            *lo = Some(v);
        }
    };
    let tighten_hi = |hi: &mut Option<BigRational>, v: BigRational| {
        if hi.as_ref().is_none_or(|h| v < *h) {
            *hi = Some(v);
        }
    };
    for row in &model.rows {
        let mut fixed = BigRational::zero();
        let mut a = BigRational::zero();
        for (j, coeff) in &row.coeffs {
            if Some(*j) == cont {
                a += coeff;
            } else {
                fixed += coeff * &point[*j];
            }
        }
        if a.is_zero() {
            if row.lower.as_ref().is_some_and(|l| fixed < *l)
                || row.upper.as_ref().is_some_and(|u| fixed > *u)
            {
                return None;
            }
            continue;
        }
        let bound = |side: &BigRational| (side - &fixed) / &a;
        if let Some(l) = &row.lower {
            if a.is_positive() {
                tighten_lo(&mut lo, bound(l));
            } else {
                tighten_hi(&mut hi, bound(l));
            }
        }
        if let Some(u) = &row.upper {
            if a.is_positive() {
                tighten_hi(&mut hi, bound(u));
            } else {
                tighten_lo(&mut lo, bound(u));
            }
        }
    }
    if let (Some(l), Some(h)) = (&lo, &hi) {
        if l > h {
            return None;
        }
    }
    let mut value = model.offset.clone();
    for (j, column) in model.columns.iter().enumerate() {
        if Some(j) != cont {
            value += &column.objective * &point[j];
        }
    }
    if cont.is_none() || c.is_zero() {
        return Some(Some(value));
    }
    let wants_low = (model.sense == Sense::Min) == c.is_positive();
    let y = if wants_low { lo } else { hi };
    Some(y.map(|y| value + c * y))
}

/// The last written block: (objective text, value texts in column order).
pub(super) fn last_point(out: &str, model: &ExactProblem) -> Option<(String, Vec<String>)> {
    let start = out.rfind("\no ")? + 1;
    let mut lines = out[start..].lines();
    let objective = lines.next()?.strip_prefix("o ")?.to_string();
    let mut values = Vec::new();
    for column in &model.columns {
        let line = lines.next()?;
        let value = line.strip_prefix(&format!("v {} = ", column.name))?;
        values.push(value.to_string());
    }
    Some((objective, values))
}

/// The organizers' checker on `model_text` and the written point, when
/// `AY_MIPLIB_SOLCHECKER` names it: `Some(accepted)`.
fn referee(
    model_text: &str,
    objective: &str,
    model: &ExactProblem,
    values: &[String],
) -> Option<bool> {
    let checker = std::env::var_os("AY_MIPLIB_SOLCHECKER")?;
    // The checker asserts that a number has fewer than 32 characters.
    if model_text.split_whitespace().any(|t| t.len() > 31) {
        return None;
    }
    let dir = tempfile::tempdir().expect("tmp");
    let mps = dir.path().join("m.mps");
    let sol = dir.path().join("m.sol");
    std::fs::write(&mps, model_text).expect("write");
    let mut f = std::fs::File::create(&sol).expect("sol");
    writeln!(f, "=obj= {objective}").expect("write");
    for (column, value) in model.columns.iter().zip(values) {
        writeln!(f, "{} {value}", column.name).expect("write");
    }
    let out = std::process::Command::new(checker)
        .arg(&mps)
        .arg(&sol)
        .args(["1e-6", "1e-5"])
        .output()
        .expect("run solchecker");
    Some(
        String::from_utf8_lossy(&out.stdout)
            .contains("Check SOL: Integrality 1 Constraints 1 Objective 1"),
    )
}

/// See the module docs.
#[test]
fn test_routes_agree_with_an_exact_brute_force_on_random_mps() {
    let mut rng = Lcg(0xA1_2026_1119);
    let (mut optimal, mut infeasible, mut feasible_only, mut unknown, mut refereed) =
        (0, 0, 0, 0, 0);
    let (mut dense_false_infeasible, mut dense_rounded_points) = (0, 0);
    let tolerance = ay_lp::exact::write_tolerance();
    let mut reasons: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    for case in 0..240 {
        let Case {
            text,
            model,
            checker_reads,
        } = generate(&mut rng);
        // The reader's model is the generated one.
        let read = parse_mps_exact(&text).unwrap_or_else(|e| panic!("case {case}: {e}\n{text}"));
        let same_bounds = read.columns.iter().zip(&model.columns).all(|(a, b)| {
            a.lower == b.lower
                && a.upper == b.upper
                && a.objective == b.objective
                && a.is_integral() == b.is_integral()
        });
        let same_rows = read.rows.len() == model.rows.len()
            && read
                .rows
                .iter()
                .zip(&model.rows)
                .all(|(a, b)| a.coeffs == b.coeffs && a.lower == b.lower && a.upper == b.upper);
        assert!(
            same_bounds && same_rows && read.offset == model.offset && read.sense == model.sense,
            "case {case}: the reader's model differs from the generated one\n{text}\n{read:?}\n{model:?}"
        );
        let answer = brute_force(&model);
        let mut f = tempfile::Builder::new()
            .suffix(".mps")
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
            if checker_reads {
                if let Some(accepted) = referee(&text, objective, &model, values) {
                    assert!(accepted, "solchecker rejects the point\n{}", context());
                    refereed += 1;
                }
            }
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
        for line in out
            .lines()
            .filter(|l| l.contains("not confirmed") || l.starts_with("c stopped"))
        {
            let key: String = line.chars().take(90).collect();
            *reasons.entry(key).or_default() += 1;
        }
        match status {
            "OPTIMAL" => optimal += 1,
            "INFEASIBLE" => infeasible += 1,
            "FEASIBLE" => feasible_only += 1,
            _ => unknown += 1,
        }
        // The dense simplex on the rounded copy.
        match ay_lp::solve(&read.to_problem()) {
            Ok(sol) => {
                let values: Vec<BigRational> = sol
                    .values
                    .iter()
                    .map(|v| BigRational::from_float(*v).expect("finite"))
                    .collect();
                match (model.check_point(&values, &BigRational::zero()), &answer) {
                    (Ok(objective), Answer::Optimal(v)) => {
                        let gap = match model.sense {
                            Sense::Min => v - &objective,
                            Sense::Max => &objective - v,
                        };
                        assert!(
                            !gap.is_positive(),
                            "dense point better than the optimum\n{}",
                            context()
                        );
                    }
                    (Ok(_), Answer::Infeasible) => {
                        panic!("dense point in an infeasible model\n{}", context())
                    }
                    _ => dense_rounded_points += 1,
                }
            }
            Err(ay_lp::LpError::Infeasible) if matches!(answer, Answer::Optimal(_)) => {
                dense_false_infeasible += 1;
            }
            Err(_) => {}
        }
    }
    eprintln!(
        "route: {optimal} optimal, {infeasible} infeasible, {feasible_only} feasible only, \
         {unknown} unknown; points checked by solchecker: {refereed}; dense simplex on the \
         rounded copy: {dense_false_infeasible} false infeasible, {dense_rounded_points} points \
         not exactly feasible or not optimal; unconfirmed: {reasons:#?}"
    );
    assert!(
        optimal >= 60 && infeasible >= 20,
        "too few confirmed verdicts: {optimal} {infeasible}"
    );
}
