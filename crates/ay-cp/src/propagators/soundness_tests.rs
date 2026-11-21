// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Brute-force soundness check of every propagator's explanations.
//!
//! The SAT core keeps every clause a propagator returns (a propagation
//! reason or a conflict) as a learned clause for the rest of the run, also
//! across the incremental solves of an optimisation loop. Such a clause must
//! therefore hold in EVERY solution of the constraint over the root domains,
//! not only in the solutions that agree with the search state it was derived
//! in. One clause that a real solution falsifies cuts that solution off for
//! good: a false UNSAT, a false optimality claim or a lost solution under
//! `-a` (AY-N8, MiniZinc Challenge rect-euler/3venn, 2026-11-18).
//!
//! The harness takes a constraint instance (root domains, the constraint's
//! meaning as a predicate on values, and a builder for its propagator),
//! enumerates every solution, then drives one propagator instance through
//! random search states the way the engine does: tighten bounds at new
//! decision levels, run the propagator to a fixpoint applying each
//! conclusion, backtrack, and again. Every clause it returns is checked
//! against every solution, and for its shape (a conflict is false on the
//! trail; a propagation has at most one literal that is not false).
//!
//! A propagator gets the test by adding one generator to [`REGISTRY`].

use ay_sat::{Literal, Solver as SatSolver};

use crate::domain::Domain;
use crate::encoder::IntegerEncoder;
use crate::propagator::{PropagationResult, Propagator};
use crate::trail::IntegerTrail;
use crate::variable::IntVarId;

use super::alldifferent::AllDifferentBounds;
use super::alldifferent_ac::AllDifferentAc;
use super::cumulative::Cumulative;
use super::disjunctive::Disjunctive;
use super::div::Div;
use super::element::Element;
use super::linear::LinearLe;
use super::linear_ne::LinearNotEqual;
use super::shifted_alldifferent::ShiftedAllDifferentBounds;
use super::table::Table;
use super::times::Times;

/// xorshift64*: a fixed-seed generator, so a failure names its seed.
pub(crate) struct Rng(pub(crate) u64);

impl Rng {
    pub(crate) fn from_seed(seed: u64) -> Self {
        Self(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1)
    }

    pub(crate) fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    /// Uniform in `lo..=hi`.
    pub(crate) fn range(&mut self, lo: i64, hi: i64) -> i64 {
        let span = u64::try_from(hi - lo + 1).expect("non-empty range");
        lo + i64::try_from(self.next() % span).expect("small range")
    }

    pub(crate) fn index(&mut self, len: usize) -> usize {
        usize::try_from(self.next() % u64::try_from(len).expect("small")).expect("small")
    }

    /// True with probability `percent` / 100.
    pub(crate) fn chance(&mut self, percent: u64) -> bool {
        self.next() % 100 < percent
    }
}

/// Where a generator's values lie: its small template window around zero,
/// or that window moved against `i64::MIN` or against `i64::MAX`. At the
/// ends, `x + 1`, `x - 1`, `s + d`, `x + shift` and sums of terms leave the
/// i64 range, which the code under test must handle without a panic (debug
/// builds) or a wrap (release builds).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum End {
    Zero,
    Min,
    Max,
}

impl End {
    /// The two ends of the i64 range.
    pub(crate) const BOTH: [Self; 2] = [Self::Min, Self::Max];
}

/// A shift that moves a template window `lo..=hi` to an [`End`]: unchanged
/// for `End::Zero`, starting at `i64::MIN`, or ending at `i64::MAX`. Every
/// value a generator draws in the template window is moved by the same
/// shift, so related values (domains, tuples, right-hand sides) keep their
/// relation.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Place {
    shift: i128,
}

impl Place {
    pub(crate) fn new(end: End, lo: i64, hi: i64) -> Self {
        let shift = match end {
            End::Zero => 0,
            End::Min => i128::from(i64::MIN) - i128::from(lo),
            End::Max => i128::from(i64::MAX) - i128::from(hi),
        };
        Self { shift }
    }

    /// The shift, for values derived from several placed ones.
    pub(crate) fn shift(self) -> i128 {
        self.shift
    }

    /// Template value `v` (inside the window) moved to the end.
    pub(crate) fn at(self, v: i64) -> i64 {
        i64::try_from(i128::from(v) + self.shift).expect("value inside the placed window")
    }

    /// [`random_domain`] in the template window `lo..=hi`, moved.
    pub(crate) fn domain(self, rng: &mut Rng, lo: i64, hi: i64) -> Vec<i64> {
        random_domain(rng, lo, hi)
            .into_iter()
            .map(|v| self.at(v))
            .collect()
    }

    /// `rng.range(lo, hi)`, moved.
    pub(crate) fn range(self, rng: &mut Rng, lo: i64, hi: i64) -> i64 {
        self.at(rng.range(lo, hi))
    }
}

/// `value` clamped into i64 (a right-hand side beyond every reachable sum).
pub(crate) fn clamp_i64(value: i128) -> i64 {
    i64::try_from(value).unwrap_or(if value < 0 { i64::MIN } else { i64::MAX })
}

/// `coeffs . x` without overflow.
pub(crate) fn dot_wide(coeffs: &[i64], x: &[i64]) -> i128 {
    coeffs
        .iter()
        .zip(x)
        .map(|(&c, &x)| i128::from(c) * i128::from(x))
        .sum()
}

/// The meaning of a constraint: does this assignment of the instance's
/// variables (indexed like `Case::domains`) satisfy it?
type Holds = Box<dyn Fn(&[i64]) -> bool>;
/// Builds the propagator over the instance's variables.
type Build = Box<dyn Fn(&[IntVarId]) -> Box<dyn Propagator>>;

/// One constraint instance.
pub(crate) struct Case {
    /// Root domain of each variable (sorted, distinct values).
    domains: Vec<Vec<i64>>,
    holds: Holds,
    build: Build,
    /// Human-readable description for failure messages.
    label: String,
}

/// A random root domain: an interval inside `lo..=hi`, sometimes with holes,
/// sometimes a single value (a constant).
fn random_domain(rng: &mut Rng, lo: i64, hi: i64) -> Vec<i64> {
    if rng.chance(10) {
        return vec![rng.range(lo, hi)];
    }
    let a = rng.range(lo, hi);
    let b = rng.range(a, hi);
    let mut values: Vec<i64> = (a..=b).collect();
    if values.len() > 2 && rng.chance(30) {
        let keep_first = values[0];
        let keep_last = values[values.len() - 1];
        values.retain(|&v| v == keep_first || v == keep_last || !rng.chance(35));
    }
    values
}

/// Positions of a constraint mapped onto variables; with some probability
/// two positions share a variable (FlatZinc front ends share one fixed
/// variable per constant, and a model may repeat a variable).
fn scope(rng: &mut Rng, positions: usize, alias_percent: u64) -> (usize, Vec<usize>) {
    let mut map = Vec::with_capacity(positions);
    let mut n = 0;
    for _ in 0..positions {
        if n > 0 && rng.chance(alias_percent) {
            map.push(rng.index(n));
        } else {
            map.push(n);
            n += 1;
        }
    }
    (n, map)
}

fn pick(values: &[i64], map: &[usize]) -> Vec<i64> {
    map.iter().map(|&i| values[i]).collect()
}

fn vars_of(vars: &[IntVarId], map: &[usize]) -> Vec<IntVarId> {
    map.iter().map(|&i| vars[i]).collect()
}

// ---------------------------------------------------------------- generators
//
// Each generator draws its values in a small template window and moves them
// to `end` (see [`Place`]): with `End::Zero` the instances are the ones the
// generators have always drawn (same seeds, same values).

fn linear_le_case(rng: &mut Rng, end: End) -> Case {
    let positions = usize::try_from(rng.range(1, 4)).expect("small");
    let (n, map) = scope(rng, positions, 10);
    let place = Place::new(end, -4, 6);
    let domains = (0..n).map(|_| place.domain(rng, -4, 6)).collect();
    let coeffs: Vec<i64> = map
        .iter()
        .map(|_| {
            let c = rng.range(-4, 4);
            if c == 0 && !rng.chance(10) {
                1
            } else {
                c
            }
        })
        .collect();
    // The template right-hand side, moved with the variables.
    let total: i128 = coeffs.iter().map(|&c| i128::from(c)).sum();
    let rhs = clamp_i64(i128::from(rng.range(-12, 12)) + total * place.shift());
    let label = format!("linear_le {coeffs:?} . x <= {rhs}, scope {map:?}");
    let c2 = coeffs.clone();
    let m2 = map.clone();
    Case {
        domains,
        holds: Box::new(move |v| dot_wide(&c2, &pick(v, &m2)) <= i128::from(rhs)),
        build: Box::new(move |vars| {
            Box::new(LinearLe::new(coeffs.clone(), vars_of(vars, &map), rhs))
        }),
        label,
    }
}

fn linear_ne_case(rng: &mut Rng, end: End) -> Case {
    let positions = usize::try_from(rng.range(1, 4)).expect("small");
    let (n, map) = scope(rng, positions, 10);
    let place = Place::new(end, -3, 5);
    let domains = (0..n).map(|_| place.domain(rng, -3, 5)).collect();
    let coeffs: Vec<i64> = map.iter().map(|_| rng.range(-3, 3)).collect();
    let total: i128 = coeffs.iter().map(|&c| i128::from(c)).sum();
    let rhs = clamp_i64(i128::from(rng.range(-6, 6)) + total * place.shift());
    let label = format!("linear_ne {coeffs:?} . x != {rhs}, scope {map:?}");
    let c2 = coeffs.clone();
    let m2 = map.clone();
    Case {
        domains,
        holds: Box::new(move |v| dot_wide(&c2, &pick(v, &m2)) != i128::from(rhs)),
        build: Box::new(move |vars| {
            Box::new(LinearNotEqual::new(
                coeffs.clone(),
                vars_of(vars, &map),
                rhs,
            ))
        }),
        label,
    }
}

fn distinct(x: &[i64]) -> bool {
    (0..x.len()).all(|i| ((i + 1)..x.len()).all(|j| x[i] != x[j]))
}

fn alldifferent_case(rng: &mut Rng, end: End) -> Case {
    let n = usize::try_from(rng.range(2, 5)).expect("small");
    let place = Place::new(end, 0, 5);
    let domains = (0..n).map(|_| place.domain(rng, 0, 5)).collect();
    Case {
        domains,
        holds: Box::new(distinct),
        build: Box::new(|vars| Box::new(AllDifferentBounds::new(vars.to_vec()))),
        label: "alldifferent (bounds)".to_string(),
    }
}

fn alldifferent_ac_case(rng: &mut Rng, end: End) -> Case {
    let n = usize::try_from(rng.range(3, 5)).expect("small");
    let place = Place::new(end, 0, 5);
    let domains: Vec<Vec<i64>> = (0..n).map(|_| place.domain(rng, 0, 5)).collect();
    let mut union: Vec<i64> = domains.iter().flatten().copied().collect();
    union.sort_unstable();
    union.dedup();
    Case {
        domains,
        holds: Box::new(distinct),
        build: Box::new(move |vars| Box::new(AllDifferentAc::new(vars.to_vec(), union.clone()))),
        label: "alldifferent (AC)".to_string(),
    }
}

fn shifted_alldifferent_case(rng: &mut Rng, end: End) -> Case {
    let n = usize::try_from(rng.range(2, 5)).expect("small");
    let place = Place::new(end, 0, 5);
    let domains = (0..n).map(|_| place.domain(rng, 0, 5)).collect();
    let shifts: Vec<i64> = (0..n).map(|_| rng.range(-3, 3)).collect();
    let label = format!("shifted alldifferent, shifts {shifts:?}");
    let s2 = shifts.clone();
    Case {
        domains,
        holds: Box::new(move |v| {
            // `x + shift` may leave i64 at the ends: compare in i128.
            let x: Vec<i128> = v
                .iter()
                .zip(&s2)
                .map(|(&v, &s)| i128::from(v) + i128::from(s))
                .collect();
            (0..x.len()).all(|i| ((i + 1)..x.len()).all(|j| x[i] != x[j]))
        }),
        build: Box::new(move |vars| {
            Box::new(ShiftedAllDifferentBounds::new(
                vars.to_vec(),
                shifts.clone(),
            ))
        }),
        label,
    }
}

fn element_case(rng: &mut Rng, end: End) -> Case {
    let len = usize::try_from(rng.range(1, 4)).expect("small");
    // Positions: index, result, array[0..len].
    let (n, map) = scope(rng, len + 2, 8);
    let place = Place::new(end, -2, 5);
    let mut domains: Vec<Vec<i64>> = (0..n).map(|_| place.domain(rng, -2, 5)).collect();
    // Index domain: mostly in range, sometimes reaching past either end; at
    // an end of i64, sometimes there too (no position at all).
    let top = i64::try_from(len).expect("small");
    domains[map[0]] = if end != End::Zero && rng.chance(30) {
        Place::new(end, -1, top).domain(rng, -1, top)
    } else {
        random_domain(rng, -1, top)
    };
    let label = format!("element, len {len}, scope {map:?}");
    let m2 = map.clone();
    Case {
        domains,
        holds: Box::new(move |v| {
            let x = pick(v, &m2);
            let (index, result) = (x[0], x[1]);
            usize::try_from(index)
                .ok()
                .and_then(|i| x[2..].get(i))
                .is_some_and(|&a| a == result)
        }),
        build: Box::new(move |vars| {
            let x = vars_of(vars, &map);
            Box::new(Element::new(x[0], x[2..].to_vec(), x[1]))
        }),
        label,
    }
}

fn table_case(rng: &mut Rng, end: End) -> Case {
    let n = usize::try_from(rng.range(1, 3)).expect("small");
    // Tuples reach one value past the domains on each side.
    let place = Place::new(end, -1, 5);
    let domains = (0..n).map(|_| place.domain(rng, 0, 4)).collect();
    let tuples: Vec<Vec<i64>> = (0..rng.range(0, 8))
        .map(|_| (0..n).map(|_| place.range(rng, -1, 5)).collect())
        .collect();
    let label = format!("table {tuples:?}");
    let t2 = tuples.clone();
    Case {
        domains,
        holds: Box::new(move |v| t2.iter().any(|t| t.as_slice() == v)),
        build: Box::new(move |vars| Box::new(Table::new(vars.to_vec(), tuples.clone()))),
        label,
    }
}

/// Does `[s, s + d)` contain `t`? (In i128: `s + d` may pass `i64::MAX`.)
fn runs_at(s: i64, d: i64, t: i128) -> bool {
    i128::from(s) <= t && t < i128::from(s) + i128::from(d)
}

/// The load only rises at a start time, so those are the times checked.
fn cumulative_holds(starts: &[i64], durations: &[i64], demands: &[i64], capacity: i64) -> bool {
    starts.iter().map(|&s| i128::from(s)).all(|t| {
        (0..starts.len())
            .filter(|&i| runs_at(starts[i], durations[i], t))
            .map(|i| i128::from(demands[i]))
            .sum::<i128>()
            <= i128::from(capacity)
    })
}

fn cumulative_case(rng: &mut Rng, end: End) -> Case {
    let tasks = usize::try_from(rng.range(1, 4)).expect("small");
    let horizon = rng.range(4, 10);
    let capacity = rng.range(0, 4);
    // Start times move to the end; durations and demands stay small, so at
    // `End::Max` a task may run past `i64::MAX`.
    let place = Place::new(end, 0, horizon);
    // Positions: starts, durations, demands. Durations and demands are often
    // constants, and constants are often shared.
    let mut domains: Vec<Vec<i64>> = Vec::new();
    let mut map = Vec::with_capacity(3 * tasks);
    for _ in 0..tasks {
        domains.push(place.domain(rng, 0, horizon));
        map.push(domains.len() - 1);
    }
    for kind in 0..2 {
        for _ in 0..tasks {
            let constant = rng.chance(70);
            let dom = if constant {
                let v = if kind == 0 {
                    rng.range(0, 5)
                } else {
                    rng.range(0, 3)
                };
                vec![v]
            } else if kind == 0 {
                random_domain(rng, 0, 4)
            } else {
                random_domain(rng, 0, 3)
            };
            let shared = (dom.len() == 1)
                .then(|| domains.iter().position(|d| *d == dom))
                .flatten()
                .filter(|_| rng.chance(50));
            if let Some(i) = shared {
                map.push(i);
            } else {
                domains.push(dom);
                map.push(domains.len() - 1);
            }
        }
    }
    let label = format!("cumulative, {tasks} tasks, capacity {capacity}, scope {map:?}");
    let m2 = map.clone();
    Case {
        domains,
        holds: Box::new(move |v| {
            let x = pick(v, &m2);
            cumulative_holds(&x[..tasks], &x[tasks..2 * tasks], &x[2 * tasks..], capacity)
        }),
        build: Box::new(move |vars| {
            let x = vars_of(vars, &map);
            Box::new(Cumulative::new(
                x[..tasks].to_vec(),
                x[tasks..2 * tasks].to_vec(),
                x[2 * tasks..].to_vec(),
                capacity,
            ))
        }),
        label,
    }
}

/// No two tasks `[s, s + d)` overlap (in i128).
fn disjoint(s: &[i64], d: &[i64]) -> bool {
    let end = |i: usize| i128::from(s[i]) + i128::from(d[i]);
    (0..s.len()).all(|i| {
        ((i + 1)..s.len()).all(|j| end(i) <= i128::from(s[j]) || end(j) <= i128::from(s[i]))
    })
}

fn disjunctive_case(rng: &mut Rng, end: End) -> Case {
    let n = usize::try_from(rng.range(2, 4)).expect("small");
    let horizon = rng.range(5, 12);
    let place = Place::new(end, 0, horizon);
    let domains = (0..n).map(|_| place.domain(rng, 0, horizon)).collect();
    let durations: Vec<i64> = (0..n).map(|_| rng.range(1, 5)).collect();
    let label = format!("disjunctive, durations {durations:?}");
    let d2 = durations.clone();
    Case {
        domains,
        holds: Box::new(move |s| disjoint(s, &d2)),
        build: Box::new(move |vars| Box::new(Disjunctive::new(vars.to_vec(), durations.clone()))),
        label,
    }
}

/// A generator of random small instances, at the given end of i64.
pub(crate) type Generate = fn(&mut Rng, End) -> Case;

/// Every propagator in `crate::propagators`, with a generator of random
/// small instances. A new propagator registers itself here.
/// `x * y = result` (or `x div y = result`) over random domains; a
/// position may share a variable with another (`x * x = r`, `x div y = x`).
fn arithmetic_case(rng: &mut Rng, divide: bool) -> Case {
    let (n, map) = scope(rng, 3, 15);
    let domains = (0..n)
        .map(|_| {
            if rng.chance(40) {
                random_domain(rng, -4, 5)
            } else if divide {
                random_domain(rng, -7, 7)
            } else {
                random_domain(rng, -12, 16)
            }
        })
        .collect();
    let m2 = map.clone();
    let name = if divide { "div" } else { "times" };
    let label = format!("{name}, scope {map:?}");
    Case {
        domains,
        holds: Box::new(move |v| {
            let x = pick(v, &m2);
            let (a, b, r) = (i128::from(x[0]), i128::from(x[1]), i128::from(x[2]));
            if divide {
                b != 0 && a / b == r
            } else {
                a * b == r
            }
        }),
        build: Box::new(move |vars| {
            let v = vars_of(vars, &map);
            if divide {
                Box::new(Div::new(v[0], v[1], v[2]))
            } else {
                Box::new(Times::new(v[0], v[1], v[2]))
            }
        }),
        label,
    }
}

// The two arithmetic families are not moved to the ends of i64: a product
// of two values there is not representable, so `end` is ignored and the
// instances are the same at every end.
fn times_case(rng: &mut Rng, _end: End) -> Case {
    arithmetic_case(rng, false)
}

fn div_case(rng: &mut Rng, _end: End) -> Case {
    arithmetic_case(rng, true)
}

pub(crate) const REGISTRY: &[(&str, Generate)] = &[
    ("linear", linear_le_case),
    ("linear_ne", linear_ne_case),
    ("alldifferent", alldifferent_case),
    ("alldifferent_ac", alldifferent_ac_case),
    ("shifted_alldifferent", shifted_alldifferent_case),
    ("element", element_case),
    ("table", table_case),
    ("cumulative", cumulative_case),
    ("disjunctive", disjunctive_case),
    ("times", times_case),
    ("div", div_case),
];

// ------------------------------------------------------------------- harness

/// Brute force is limited to instances with at most this many assignments.
const MAX_ASSIGNMENTS: usize = 40_000;

struct Instance {
    trail: IntegerTrail,
    encoder: IntegerEncoder,
    vars: Vec<IntVarId>,
    solutions: Vec<Vec<i64>>,
}

/// A clause falsified by a solution, or with a shape the SAT core cannot use.
#[derive(Debug)]
pub(crate) struct Fault {
    pub(crate) message: String,
}

impl Instance {
    fn new(case: &Case) -> Option<Self> {
        let mut total: usize = 1;
        for d in &case.domains {
            total = total.checked_mul(d.len())?;
            if total > MAX_ASSIGNMENTS {
                return None;
            }
        }
        let mut trail = IntegerTrail::new();
        let mut encoder = IntegerEncoder::new();
        let mut sat = SatSolver::new(0);
        let vars = case
            .domains
            .iter()
            .map(|values| {
                let var = trail.register_domain(Domain::from_values(values));
                let enc = encoder.register_var(values[0], values[values.len() - 1]);
                assert_eq!(var, enc);
                var
            })
            .collect();
        encoder.pre_allocate_all(&mut sat);
        let mut solutions = Vec::new();
        let mut current = vec![0; case.domains.len()];
        enumerate(&case.domains, 0, &mut current, &case.holds, &mut solutions);
        Some(Self {
            trail,
            encoder,
            vars,
            solutions,
        })
    }

    fn var_index(&self, var: IntVarId) -> usize {
        self.vars
            .iter()
            .position(|&v| v == var)
            .expect("literal on an instance variable")
    }

    /// `(variable index, value, positive)` of an order literal `[x >= value]`.
    fn decode(&self, lit: Literal) -> Result<(usize, i64), Fault> {
        let bound = self.encoder.decode(lit.variable()).ok_or_else(|| Fault {
            message: format!("literal {lit:?} is not an order-encoding literal"),
        })?;
        assert!(bound.is_ge);
        Ok((self.var_index(bound.var), bound.value))
    }

    fn holds_in(&self, lit: Literal, values: &[i64]) -> Result<bool, Fault> {
        let (i, value) = self.decode(lit)?;
        Ok((values[i] >= value) == lit.is_positive())
    }

    /// Truth of `lit` on the current trail, `None` if unassigned.
    fn on_trail(&self, lit: Literal) -> Result<Option<bool>, Fault> {
        let (i, value) = self.decode(lit)?;
        let var = self.vars[i];
        let ge = if self.trail.lb(var) >= value {
            Some(true)
        } else if self.trail.ub(var) < value {
            Some(false)
        } else {
            None
        };
        Ok(ge.map(|g| g == lit.is_positive()))
    }

    fn describe(&self, clause: &[Literal]) -> String {
        clause
            .iter()
            .map(|&lit| match self.decode(lit) {
                Ok((i, value)) if lit.is_positive() => format!("[x{i} >= {value}]"),
                Ok((i, value)) => format!("[x{i} <= {}]", i128::from(value) - 1),
                Err(_) => format!("{lit:?}"),
            })
            .collect::<Vec<_>>()
            .join(" | ")
    }

    fn state(&self) -> String {
        self.vars
            .iter()
            .enumerate()
            .map(|(i, &v)| format!("x{i} in [{}, {}]", self.trail.lb(v), self.trail.ub(v)))
            .collect::<Vec<_>>()
            .join(", ")
    }

    /// Check one clause; returns the literal a propagation clause concludes
    /// (its only literal that is not false on the trail), if unassigned.
    fn check_clause(&self, conflict: bool, clause: &[Literal]) -> Result<Option<Literal>, Fault> {
        let kind = if conflict { "conflict" } else { "reason" };
        for values in &self.solutions {
            let mut satisfied = false;
            for &lit in clause {
                if self.holds_in(lit, values)? {
                    satisfied = true;
                    break;
                }
            }
            if !satisfied {
                return Err(Fault {
                    message: format!(
                        "{kind} clause {} is falsified by the solution {values:?} \
                         (state: {})",
                        self.describe(clause),
                        self.state()
                    ),
                });
            }
        }
        let mut open = Vec::new();
        for &lit in clause {
            match self.on_trail(lit)? {
                Some(false) => {}
                Some(true) => open.push((lit, true)),
                None => open.push((lit, false)),
            }
        }
        // A propagation concludes one bound, or removes one interior value
        // (`[x <= v - 1] | [x >= v + 1]`: two open literals on one variable).
        let same_var = open.iter().all(|&(lit, _)| {
            self.decode(lit).ok().map(|d| d.0) == self.decode(open[0].0).ok().map(|d| d.0)
        });
        let shape_ok = if conflict {
            open.is_empty()
        } else {
            open.len() <= 1 || (open.len() == 2 && same_var)
        };
        if !shape_ok {
            return Err(Fault {
                message: format!(
                    "{kind} clause {} has {} literals that are not false on the trail \
                     (state: {})",
                    self.describe(clause),
                    open.len(),
                    self.state()
                ),
            });
        }
        Ok(match open.as_slice() {
            [(lit, false)] => Some(*lit),
            _ => None,
        })
    }

    /// Apply a concluded literal to the trail; `false` on a wipeout.
    fn apply(&mut self, lit: Literal) -> bool {
        let (i, value) = self.decode(lit).expect("checked");
        let var = self.vars[i];
        let result = if lit.is_positive() {
            self.trail.set_lb(var, value, lit, None)
        } else {
            // `not [x >= i64::MIN]` is false in every state: a wipeout.
            let Some(ub) = value.checked_sub(1) else {
                return false;
            };
            self.trail.set_ub(var, ub, lit, None)
        };
        result.is_ok()
    }

    /// Tighten a random variable at a new decision level.
    fn decide(&mut self, rng: &mut Rng) {
        self.trail.push_level();
        let i = rng.index(self.vars.len());
        let var = self.vars[i];
        let values: Vec<i64> = self
            .trail
            .values(var)
            .into_iter()
            .filter(|&v| v >= self.trail.lb(var) && v <= self.trail.ub(var))
            .collect();
        if values.len() < 2 {
            return;
        }
        let a = rng.index(values.len());
        let b = a + rng.index(values.len() - a);
        let (lb, ub) = (values[a], values[b]);
        let ge = self.encoder.lookup_ge(var, lb).expect("ge literal");
        let le = self.encoder.lookup_le(var, ub).expect("le literal");
        self.trail.set_lb(var, lb, ge, None).expect("lb in domain");
        self.trail.set_ub(var, ub, le, None).expect("ub in domain");
    }
}

fn enumerate(
    domains: &[Vec<i64>],
    k: usize,
    current: &mut [i64],
    holds: &Holds,
    out: &mut Vec<Vec<i64>>,
) {
    if k == domains.len() {
        if holds(current) {
            out.push(current.to_vec());
        }
        return;
    }
    for &v in &domains[k] {
        current[k] = v;
        enumerate(domains, k + 1, current, holds, out);
    }
}

/// Statistics of one harness run.
#[derive(Debug, Default)]
pub(crate) struct Exercised {
    pub(crate) instances: usize,
    pub(crate) reasons: usize,
    pub(crate) conflicts: usize,
}

/// Drive the propagator of `case` through random search states.
fn exercise(case: &Case, rng: &mut Rng, stats: &mut Exercised) -> Result<(), Fault> {
    let Some(mut inst) = Instance::new(case) else {
        return Ok(());
    };
    stats.instances += 1;
    let mut prop = (case.build)(&inst.vars);
    for _episode in 0..4 {
        for _ in 0..rng.range(0, 3) {
            inst.decide(rng);
        }
        fixpoint(&mut inst, prop.as_mut(), stats)?;
        let level =
            u32::try_from(rng.index(inst.trail.current_level() as usize + 1)).expect("small level");
        inst.trail.backtrack_to(level);
    }
    Ok(())
}

/// Run the propagator to a fixpoint from the current state, checking and
/// applying every clause.
fn fixpoint(
    inst: &mut Instance,
    prop: &mut dyn Propagator,
    stats: &mut Exercised,
) -> Result<(), Fault> {
    for _round in 0..64 {
        let (conflict, clauses) = match prop.propagate(&inst.trail, &inst.encoder) {
            PropagationResult::NoChange => break,
            PropagationResult::Propagated(clauses) => (false, clauses),
            PropagationResult::Conflict(clause) => (true, vec![clause]),
        };
        // The SAT core propagates a batch clause by clause, so a later
        // clause may use an earlier one's conclusion as a reason.
        inst.trail.push_level();
        let mut progress = false;
        for clause in &clauses {
            if conflict {
                stats.conflicts += 1;
            } else {
                stats.reasons += 1;
            }
            if let Some(lit) = inst.check_clause(conflict, clause)? {
                progress = true;
                if !inst.apply(lit) {
                    return Ok(());
                }
            }
        }
        if conflict || !progress {
            break;
        }
    }
    Ok(())
}

/// Check one given state: root domains `domains`, then each `(variable,
/// lb, ub)` of `decisions` at its own decision level, then a fixpoint.
fn check_state(
    domains: &[&[i64]],
    holds: Holds,
    build: Build,
    decisions: &[(usize, i64, i64)],
) -> Result<Exercised, String> {
    let case = Case {
        domains: domains.iter().map(|d| d.to_vec()).collect(),
        holds,
        build,
        label: String::new(),
    };
    let mut inst = Instance::new(&case).ok_or("instance too large")?;
    let mut prop = (case.build)(&inst.vars);
    for &(i, lb, ub) in decisions {
        inst.trail.push_level();
        let var = inst.vars[i];
        let ge = inst.encoder.lookup_ge(var, lb).ok_or("lb literal")?;
        let le = inst.encoder.lookup_le(var, ub).ok_or("ub literal")?;
        inst.trail
            .set_lb(var, lb, ge, None)
            .map_err(|_| "lb outside domain")?;
        inst.trail
            .set_ub(var, ub, le, None)
            .map_err(|_| "ub outside domain")?;
    }
    let mut stats = Exercised::default();
    fixpoint(&mut inst, prop.as_mut(), &mut stats).map_err(|f| f.message)?;
    Ok(stats)
}

/// Run `seeds` random instances of the registered generator `name`.
pub(crate) fn run(name: &str, seeds: u64) -> Result<Exercised, String> {
    run_at(name, seeds, End::Zero)
}

/// Run `seeds` random instances of the registered generator `name`, with
/// its values moved to `end`.
pub(crate) fn run_at(name: &str, seeds: u64, end: End) -> Result<Exercised, String> {
    let generate = REGISTRY
        .iter()
        .find(|(n, _)| *n == name)
        .map(|&(_, g)| g)
        .ok_or_else(|| format!("no generator {name}"))?;
    let mut stats = Exercised::default();
    for seed in 1..=seeds {
        let mut rng = Rng::from_seed(seed);
        let case = generate(&mut rng, end);
        exercise(&case, &mut rng, &mut stats).map_err(|fault| {
            format!(
                "{name} seed {seed} at {end:?}: {} (domains {:?}): {}",
                case.label, case.domains, fault.message
            )
        })?;
    }
    Ok(stats)
}

fn check_registered(name: &str) {
    match run(name, 3000) {
        Ok(stats) => {
            assert!(
                stats.instances > 1000 && stats.reasons + stats.conflicts > 300,
                "{name}: too little exercised: {stats:?}"
            );
        }
        Err(message) => panic!("{message}"),
    }
}

/// Every propagator, with its values against `i64::MIN` and against
/// `i64::MAX`: bounds at the ends, `x + 1` past them, sums beyond i64.
/// The clauses must hold in every solution there too, and no propagator may
/// panic on an overflow (debug builds) or wrap (release builds).
#[test]
fn test_every_propagator_at_the_ends_of_i64() {
    let mut failures = Vec::new();
    for &(name, _) in REGISTRY {
        for end in End::BOTH {
            // A panic (an overflow in a debug build) is a failure of this
            // propagator at this end; the others still run.
            let outcome = std::panic::catch_unwind(|| run_at(name, 800, end))
                .unwrap_or_else(|_| Err(format!("{name} at {end:?}: panicked (see stderr)")));
            match outcome {
                Ok(stats) => {
                    if stats.instances < 200 || stats.reasons + stats.conflicts < 50 {
                        failures.push(format!(
                            "{name} at {end:?}: too little exercised: {stats:?}"
                        ));
                    }
                }
                Err(message) => failures.push(message),
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// Every propagator module declared in `propagators/mod.rs` has a
/// generator in [`REGISTRY`] under its module name.
#[test]
fn test_registry_names_every_propagator() {
    let modules: Vec<&str> = include_str!("mod.rs")
        .lines()
        .filter_map(|l| l.trim().strip_prefix("pub mod "))
        .filter_map(|l| l.strip_suffix(';'))
        .collect();
    assert!(modules.len() >= 9, "module list not found: {modules:?}");
    for module in modules {
        assert!(
            REGISTRY.iter().any(|(n, _)| *n == module),
            "propagator module {module} has no soundness generator in REGISTRY"
        );
    }
}

#[test]
fn test_linear_le_clauses_hold_in_every_solution() {
    check_registered("linear");
}

#[test]
fn test_linear_ne_clauses_hold_in_every_solution() {
    check_registered("linear_ne");
}

#[test]
fn test_alldifferent_clauses_hold_in_every_solution() {
    check_registered("alldifferent");
}

#[test]
fn test_alldifferent_ac_clauses_hold_in_every_solution() {
    check_registered("alldifferent_ac");
}

#[test]
fn test_shifted_alldifferent_clauses_hold_in_every_solution() {
    check_registered("shifted_alldifferent");
}

#[test]
fn test_element_clauses_hold_in_every_solution() {
    check_registered("element");
}

#[test]
fn test_table_clauses_hold_in_every_solution() {
    check_registered("table");
}

#[test]
fn test_cumulative_clauses_hold_in_every_solution() {
    check_registered("cumulative");
}

#[test]
fn test_disjunctive_clauses_hold_in_every_solution() {
    check_registered("disjunctive");
}

#[test]
fn test_times_clauses_hold_in_every_solution() {
    check_registered("times");
}

#[test]
fn test_div_clauses_hold_in_every_solution() {
    check_registered("div");
}

// ------------------------------------------------- regressions (2026-11-18)

/// Task 1 (`d = 1`, demand 2) is fixed at 8 and fills the capacity there,
/// so task 0 (`d = 2`, demand 2) must end by 8: `s0 <= 6`. The backward
/// pass found that from the overload at time 8, past `lst(s0) = 7`, but
/// explained it with the tasks running in `[7, 7]` only, so the reason
/// left task 1 out: `[s0 >= 8] | [s0 <= 6]`, which `s0 = 7, s1 = 3`
/// falsifies. The window is `[new_lst + 1, lst + d - 1] = [7, 8]`.
#[test]
fn test_cumulative_backward_reason_names_the_blocking_task() {
    // Variables: s0, s1, then the constants 2 (d0), 1 (d1), 2 (demands).
    let stats = check_state(
        &[&[3, 4, 5, 6, 7], &[3, 4, 5, 6, 7, 8, 9], &[2], &[1], &[2]],
        Box::new(|x| cumulative_holds(&x[..2], &[x[2], x[3]], &[x[4], x[4]], 2)),
        Box::new(|v| {
            Box::new(Cumulative::new(
                v[..2].to_vec(),
                vec![v[2], v[3]],
                vec![v[4], v[4]],
                2,
            ))
        }),
        &[(1, 8, 8)],
    );
    let stats = stats.unwrap_or_else(|e| panic!("{e}"));
    assert!(stats.reasons > 0, "s0 <= 6 must still be derived");
}

/// An index whose upper bound drops below 0 (no position left) must give a
/// conflict. Before 2026-11-18 the clamped bound `-1` was cast to `usize`
/// before the emptiness test, wrapped to `usize::MAX`, and the propagator
/// indexed past the array: a panic.
#[test]
fn test_element_negative_index_bound_is_a_conflict() {
    // Variables: index, result, array[0].
    let stats = check_state(
        &[&[-2, -1, 0], &[0, 1], &[0, 1]],
        Box::new(|x| x[0] == 0 && x[2] == x[1]),
        Box::new(|v| Box::new(Element::new(v[0], vec![v[2]], v[1]))),
        &[(0, -2, -1)],
    );
    let stats = stats.unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(stats.conflicts, 1);
}

/// The value 2 is a hole of x1's root domain. Table and AllDifferentAc
/// "explained" each hole `w` with the literal `[x >= w + 1]`, false on the
/// trail: the conflict below had a literal that was not false (a conflict
/// that is none), and pruning clauses were not unit. Root holes are
/// permanent and need no reason.
#[test]
fn test_table_conflict_with_a_root_hole_is_false_on_the_trail() {
    let tuples = vec![vec![1, 1, 2], vec![4, -1, 0], vec![1, -1, 0]];
    let t = tuples.clone();
    let stats = check_state(
        &[&[4], &[0, 1, 3, 4], &[2, 3]],
        Box::new(move |x| t.iter().any(|t| t.as_slice() == x)),
        Box::new(move |v| Box::new(Table::new(v.to_vec(), tuples.clone()))),
        &[(2, 2, 2)],
    );
    let stats = stats.unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(stats.conflicts, 1);
}

/// See the table case: x3 has the root hole 1.
#[test]
fn test_alldifferent_ac_reasons_with_a_root_hole_are_false_on_the_trail() {
    let domains: [&[i64]; 4] = [&[3, 4, 5], &[1], &[4, 5], &[0, 2, 3]];
    let union = vec![0, 1, 2, 3, 4, 5];
    let stats = check_state(
        &domains,
        Box::new(distinct),
        Box::new(move |v| Box::new(AllDifferentAc::new(v.to_vec(), union.clone()))),
        &[(0, 5, 5)],
    );
    let stats = stats.unwrap_or_else(|e| panic!("{e}"));
    assert!(stats.reasons > 0);
}
