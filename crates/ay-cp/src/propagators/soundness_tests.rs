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
use super::cumulative::Cumulative;
use super::disjunctive::Disjunctive;
use super::linear::LinearLe;
use super::linear_ne::LinearNotEqual;
use super::shifted_alldifferent::ShiftedAllDifferentBounds;

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

fn linear_le_case(rng: &mut Rng) -> Case {
    let positions = usize::try_from(rng.range(1, 4)).expect("small");
    let (n, map) = scope(rng, positions, 10);
    let domains = (0..n).map(|_| random_domain(rng, -4, 6)).collect();
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
    let rhs = rng.range(-12, 12);
    let label = format!("linear_le {coeffs:?} . x <= {rhs}, scope {map:?}");
    let c2 = coeffs.clone();
    let m2 = map.clone();
    Case {
        domains,
        holds: Box::new(move |v| {
            let x = pick(v, &m2);
            c2.iter().zip(&x).map(|(c, x)| c * x).sum::<i64>() <= rhs
        }),
        build: Box::new(move |vars| {
            Box::new(LinearLe::new(coeffs.clone(), vars_of(vars, &map), rhs))
        }),
        label,
    }
}

fn linear_ne_case(rng: &mut Rng) -> Case {
    let positions = usize::try_from(rng.range(1, 4)).expect("small");
    let (n, map) = scope(rng, positions, 10);
    let domains = (0..n).map(|_| random_domain(rng, -3, 5)).collect();
    let coeffs: Vec<i64> = map.iter().map(|_| rng.range(-3, 3)).collect();
    let rhs = rng.range(-6, 6);
    let label = format!("linear_ne {coeffs:?} . x != {rhs}, scope {map:?}");
    let c2 = coeffs.clone();
    let m2 = map.clone();
    Case {
        domains,
        holds: Box::new(move |v| {
            let x = pick(v, &m2);
            c2.iter().zip(&x).map(|(c, x)| c * x).sum::<i64>() != rhs
        }),
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

fn alldifferent_case(rng: &mut Rng) -> Case {
    let n = usize::try_from(rng.range(2, 5)).expect("small");
    let domains = (0..n).map(|_| random_domain(rng, 0, 5)).collect();
    Case {
        domains,
        holds: Box::new(distinct),
        build: Box::new(|vars| Box::new(AllDifferentBounds::new(vars.to_vec()))),
        label: "alldifferent (bounds)".to_string(),
    }
}

fn shifted_alldifferent_case(rng: &mut Rng) -> Case {
    let n = usize::try_from(rng.range(2, 5)).expect("small");
    let domains = (0..n).map(|_| random_domain(rng, 0, 5)).collect();
    let shifts: Vec<i64> = (0..n).map(|_| rng.range(-3, 3)).collect();
    let label = format!("shifted alldifferent, shifts {shifts:?}");
    let s2 = shifts.clone();
    Case {
        domains,
        holds: Box::new(move |v| {
            let x: Vec<i64> = v.iter().zip(&s2).map(|(v, s)| v + s).collect();
            distinct(&x)
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

/// Does `[s, s + d)` contain `t`?
fn runs_at(s: i64, d: i64, t: i64) -> bool {
    s <= t && t < s + d
}

fn cumulative_holds(starts: &[i64], durations: &[i64], demands: &[i64], capacity: i64) -> bool {
    let lo = starts.iter().copied().min().unwrap_or(0);
    let hi = starts
        .iter()
        .zip(durations)
        .map(|(s, d)| s + d)
        .max()
        .unwrap_or(0);
    (lo..hi).all(|t| {
        (0..starts.len())
            .filter(|&i| runs_at(starts[i], durations[i], t))
            .map(|i| demands[i])
            .sum::<i64>()
            <= capacity
    })
}

fn cumulative_case(rng: &mut Rng) -> Case {
    let tasks = usize::try_from(rng.range(1, 4)).expect("small");
    let horizon = rng.range(4, 10);
    let capacity = rng.range(0, 4);
    // Positions: starts, durations, demands. Durations and demands are often
    // constants, and constants are often shared.
    let mut domains: Vec<Vec<i64>> = Vec::new();
    let mut map = Vec::with_capacity(3 * tasks);
    for _ in 0..tasks {
        domains.push(random_domain(rng, 0, horizon));
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

fn disjunctive_case(rng: &mut Rng) -> Case {
    let n = usize::try_from(rng.range(2, 4)).expect("small");
    let horizon = rng.range(5, 12);
    let domains = (0..n).map(|_| random_domain(rng, 0, horizon)).collect();
    let durations: Vec<i64> = (0..n).map(|_| rng.range(1, 5)).collect();
    let label = format!("disjunctive, durations {durations:?}");
    let d2 = durations.clone();
    Case {
        domains,
        holds: Box::new(move |s| {
            (0..s.len())
                .all(|i| ((i + 1)..s.len()).all(|j| s[i] + d2[i] <= s[j] || s[j] + d2[j] <= s[i]))
        }),
        build: Box::new(move |vars| Box::new(Disjunctive::new(vars.to_vec(), durations.clone()))),
        label,
    }
}

/// Every propagator in `crate::propagators`, with a generator of random
/// small instances. A new propagator registers itself here.
pub(crate) const REGISTRY: &[(&str, fn(&mut Rng) -> Case)] = &[
    ("linear", linear_le_case),
    ("linear_ne", linear_ne_case),
    ("alldifferent", alldifferent_case),
    ("shifted_alldifferent", shifted_alldifferent_case),
    ("cumulative", cumulative_case),
    ("disjunctive", disjunctive_case),
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
                Ok((i, value)) => format!("[x{i} <= {}]", value - 1),
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
            self.trail.set_ub(var, value - 1, lit, None)
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
    let generate = REGISTRY
        .iter()
        .find(|(n, _)| *n == name)
        .map(|&(_, g)| g)
        .ok_or_else(|| format!("no generator {name}"))?;
    let mut stats = Exercised::default();
    for seed in 1..=seeds {
        let mut rng = Rng::from_seed(seed);
        let case = generate(&mut rng);
        exercise(&case, &mut rng, &mut stats).map_err(|fault| {
            format!(
                "{name} seed {seed}: {} (domains {:?}): {}",
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
fn test_shifted_alldifferent_clauses_hold_in_every_solution() {
    check_registered("shifted_alldifferent");
}

#[test]
fn test_cumulative_clauses_hold_in_every_solution() {
    check_registered("cumulative");
}

#[test]
fn test_disjunctive_clauses_hold_in_every_solution() {
    check_registered("disjunctive");
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
