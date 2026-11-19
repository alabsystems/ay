// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Every engine constraint, solved end to end against brute force.
//!
//! The propagator harness (`propagators::soundness_tests`) checks each
//! propagator's clauses; this file checks everything else that puts clauses
//! into the SAT core: the eager encoders (`encode_alldiff_pairwise`, the
//! pigeon-hole clauses, `encode_abs`, `encode_maximum`, `encode_minimum`,
//! `encode_circuit`, `encode_inverse`, `encode_diffn`, `encode_bool_clause`,
//! `encode_pairwise_neq`), the lazily checked not-equal constraints, the
//! domain-hole clauses, blocking clauses, objective bounds and SAT-only
//! probing, on one engine reused across solves the way the FlatZinc front
//! end drives it, so every clause learned in an earlier solve stays.
//!
//! - enumeration: solve, block the solution, solve again; the solutions
//!   found must be exactly the brute-force solutions (no lost solution, no
//!   wrong one), which is what `ay flatzinc -a` prints;
//! - optimisation: solve, tighten the objective, solve again; the last
//!   objective value must be the brute-force optimum, and a probed lower
//!   bound must not pass it.

use super::*;
use crate::domain::Domain;
use crate::engine::CpSolveResult;
use crate::propagators::soundness_tests::Rng;

/// The constraint's meaning on values, given the root domains (circuit and
/// inverse number their nodes from the domains).
type Holds = Box<dyn Fn(&[i64], &[Vec<i64>]) -> bool>;
type Post = Box<dyn Fn(&[IntVarId]) -> Vec<Constraint>>;

/// A model over variables `x0..xn` with explicit root domains.
struct Model {
    domains: Vec<Vec<i64>>,
    holds: Holds,
    post: Post,
    label: String,
}

fn random_domain(rng: &mut Rng, lo: i64, hi: i64) -> Vec<i64> {
    if rng.chance(10) {
        return vec![rng.range(lo, hi)];
    }
    let a = rng.range(lo, hi);
    let b = rng.range(a, hi);
    let mut values: Vec<i64> = (a..=b).collect();
    if values.len() > 2 && rng.chance(30) {
        let (first, last) = (values[0], values[values.len() - 1]);
        values.retain(|&v| v == first || v == last || !rng.chance(35));
    }
    values
}

fn small(rng: &mut Rng, lo: i64, hi: i64) -> usize {
    usize::try_from(rng.range(lo, hi)).expect("small")
}

fn distinct(x: &[i64]) -> bool {
    (0..x.len()).all(|i| ((i + 1)..x.len()).all(|j| x[i] != x[j]))
}

fn dot(c: &[i64], x: &[i64]) -> i64 {
    c.iter().zip(x).map(|(c, x)| c * x).sum()
}

fn alldifferent_model(rng: &mut Rng) -> Model {
    let n = small(rng, 2, 5);
    Model {
        domains: (0..n).map(|_| random_domain(rng, 0, 4)).collect(),
        holds: Box::new(|x, _| distinct(x)),
        post: Box::new(|v| vec![Constraint::AllDifferent(v.to_vec())]),
        label: "alldifferent".into(),
    }
}

fn linear_model(rng: &mut Rng) -> Model {
    let n = small(rng, 1, 3);
    let coeffs: Vec<i64> = (0..n).map(|_| rng.range(-3, 3)).collect();
    let rhs = rng.range(-6, 6);
    let kind = rng.index(3);
    let c = coeffs.clone();
    Model {
        domains: (0..n).map(|_| random_domain(rng, -3, 4)).collect(),
        holds: Box::new(move |x, _| match kind {
            0 => dot(&c, x) <= rhs,
            1 => dot(&c, x) == rhs,
            _ => dot(&c, x) >= rhs,
        }),
        post: Box::new(move |v| {
            let (coeffs, vars) = (coeffs.clone(), v.to_vec());
            vec![match kind {
                0 => Constraint::LinearLe { coeffs, vars, rhs },
                1 => Constraint::LinearEq { coeffs, vars, rhs },
                _ => Constraint::LinearGe { coeffs, vars, rhs },
            }]
        }),
        label: format!("linear kind {kind}"),
    }
}

fn linear_ne_model(rng: &mut Rng) -> Model {
    let n = small(rng, 1, 3);
    let coeffs: Vec<i64> = (0..n).map(|_| rng.range(-3, 3)).collect();
    let rhs = rng.range(-4, 4);
    let c = coeffs.clone();
    Model {
        domains: (0..n).map(|_| random_domain(rng, -2, 3)).collect(),
        holds: Box::new(move |x, _| dot(&c, x) != rhs),
        post: Box::new(move |v| {
            vec![Constraint::LinearNotEqual {
                coeffs: coeffs.clone(),
                vars: v.to_vec(),
                rhs,
            }]
        }),
        label: "linear_ne".into(),
    }
}

fn pairwise_neq_model(rng: &mut Rng) -> Model {
    let offset = rng.range(-3, 3);
    // Wide domains take the lazy path (checked on complete assignments).
    let wide = rng.chance(30);
    let domains = if wide {
        vec![(0..=70).collect(), (0..=70).collect::<Vec<i64>>()]
    } else {
        vec![random_domain(rng, 0, 5), random_domain(rng, 0, 5)]
    };
    Model {
        domains,
        holds: Box::new(move |x, _| x[0] - x[1] != offset),
        post: Box::new(move |v| {
            vec![Constraint::PairwiseNeq {
                x: v[0],
                y: v[1],
                offset,
            }]
        }),
        label: format!("pairwise_neq offset {offset}, wide {wide}"),
    }
}

fn element_model(rng: &mut Rng) -> Model {
    let len = small(rng, 1, 3);
    let mut domains = vec![random_domain(
        rng,
        0,
        i64::try_from(len).expect("small") - 1,
    )];
    domains.extend((0..=len).map(|_| random_domain(rng, 0, 3)));
    Model {
        domains,
        holds: Box::new(move |x, _| {
            usize::try_from(x[0])
                .ok()
                .and_then(|i| x[2..].get(i))
                .is_some_and(|&a| a == x[1])
        }),
        post: Box::new(|v| {
            vec![Constraint::Element {
                index: v[0],
                result: v[1],
                array: v[2..].to_vec(),
            }]
        }),
        label: format!("element len {len}"),
    }
}

fn table_model(rng: &mut Rng) -> Model {
    let n = small(rng, 1, 3);
    let tuples: Vec<Vec<i64>> = (0..rng.range(0, 6))
        .map(|_| (0..n).map(|_| rng.range(0, 3)).collect())
        .collect();
    let t = tuples.clone();
    Model {
        domains: (0..n).map(|_| random_domain(rng, 0, 3)).collect(),
        holds: Box::new(move |x, _| t.iter().any(|t| t.as_slice() == x)),
        post: Box::new(move |v| {
            vec![Constraint::Table {
                vars: v.to_vec(),
                tuples: tuples.clone(),
            }]
        }),
        label: "table".into(),
    }
}

fn cumulative_holds(s: &[i64], d: &[i64], r: &[i64], capacity: i64) -> bool {
    let hi = s.iter().zip(d).map(|(s, d)| s + d).max().unwrap_or(0);
    let lo = s.iter().copied().min().unwrap_or(0);
    (lo..hi).all(|t| {
        (0..s.len())
            .filter(|&i| s[i] <= t && t < s[i] + d[i])
            .map(|i| r[i])
            .sum::<i64>()
            <= capacity
    })
}

fn cumulative_model(rng: &mut Rng) -> Model {
    let n = small(rng, 2, 3);
    let horizon = rng.range(4, 8);
    let capacity = rng.range(1, 3);
    let mut domains: Vec<Vec<i64>> = (0..n).map(|_| random_domain(rng, 0, horizon)).collect();
    for _ in 0..n {
        domains.push(if rng.chance(70) {
            vec![rng.range(1, 4)]
        } else {
            random_domain(rng, 0, 3)
        });
    }
    for _ in 0..n {
        domains.push(if rng.chance(70) {
            vec![rng.range(1, 2)]
        } else {
            random_domain(rng, 0, 2)
        });
    }
    Model {
        domains,
        holds: Box::new(move |x, _| cumulative_holds(&x[..n], &x[n..2 * n], &x[2 * n..], capacity)),
        post: Box::new(move |v| {
            vec![Constraint::Cumulative {
                starts: v[..n].to_vec(),
                durations: v[n..2 * n].to_vec(),
                demands: v[2 * n..].to_vec(),
                capacity,
            }]
        }),
        label: format!("cumulative {n} tasks capacity {capacity}"),
    }
}

fn disjunctive_model(rng: &mut Rng) -> Model {
    let n = small(rng, 2, 3);
    let horizon = rng.range(5, 9);
    let durations: Vec<i64> = (0..n).map(|_| rng.range(1, 4)).collect();
    let d = durations.clone();
    Model {
        domains: (0..n).map(|_| random_domain(rng, 0, horizon)).collect(),
        holds: Box::new(move |s, _| {
            (0..s.len())
                .all(|i| ((i + 1)..s.len()).all(|j| s[i] + d[i] <= s[j] || s[j] + d[j] <= s[i]))
        }),
        post: Box::new(move |v| {
            vec![Constraint::Disjunctive {
                starts: v.to_vec(),
                durations: durations.clone(),
            }]
        }),
        label: "disjunctive".into(),
    }
}

fn bool_clause_model(rng: &mut Rng) -> Model {
    let n = small(rng, 1, 4);
    let positive: Vec<bool> = (0..n).map(|_| rng.chance(50)).collect();
    let p = positive.clone();
    Model {
        domains: (0..n).map(|_| random_domain(rng, 0, 1)).collect(),
        // The engine reads a Boolean as `[x >= 1]`.
        holds: Box::new(move |x, _| (0..x.len()).any(|i| (x[i] >= 1) == p[i])),
        post: Box::new(move |v| {
            let pos = (0..v.len())
                .filter(|&i| positive[i])
                .map(|i| v[i])
                .collect();
            let neg = (0..v.len())
                .filter(|&i| !positive[i])
                .map(|i| v[i])
                .collect();
            vec![Constraint::BoolClause { pos, neg }]
        }),
        label: "bool_clause".into(),
    }
}

fn abs_model(rng: &mut Rng) -> Model {
    Model {
        domains: vec![random_domain(rng, -2, 5), random_domain(rng, -5, 5)],
        holds: Box::new(|x, _| x[0] == x[1].abs()),
        post: Box::new(|v| {
            vec![Constraint::Abs {
                result: v[0],
                arg: v[1],
            }]
        }),
        label: "abs".into(),
    }
}

fn diffn_model(rng: &mut Rng) -> Model {
    let n = small(rng, 2, 2);
    // Per rectangle: x, y, dx, dy.
    let mut domains = Vec::new();
    for _ in 0..n {
        domains.push(random_domain(rng, 0, 3));
        domains.push(random_domain(rng, 0, 3));
        domains.push(random_domain(rng, 0, 2));
        domains.push(random_domain(rng, 0, 2));
    }
    Model {
        domains,
        holds: Box::new(move |v, _| {
            let r = |i: usize| (v[4 * i], v[4 * i + 1], v[4 * i + 2], v[4 * i + 3]);
            (0..n).all(|i| {
                ((i + 1)..n).all(|j| {
                    let (xi, yi, dxi, dyi) = r(i);
                    let (xj, yj, dxj, dyj) = r(j);
                    xi + dxi <= xj || xj + dxj <= xi || yi + dyi <= yj || yj + dyj <= yi
                })
            })
        }),
        post: Box::new(move |v| {
            let pick = |k: usize| (0..n).map(|i| v[4 * i + k]).collect::<Vec<_>>();
            vec![Constraint::Diffn {
                x: pick(0),
                y: pick(1),
                dx: pick(2),
                dy: pick(3),
            }]
        }),
        label: "diffn".into(),
    }
}

/// Every `Constraint` variant the engine compiles.
const MODELS: &[(&str, fn(&mut Rng) -> Model)] = &[
    ("alldifferent", alldifferent_model),
    ("linear", linear_model),
    ("linear_ne", linear_ne_model),
    ("pairwise_neq", pairwise_neq_model),
    ("element", element_model),
    ("table", table_model),
    ("cumulative", cumulative_model),
    ("disjunctive", disjunctive_model),
    ("bool_clause", bool_clause_model),
    ("abs", abs_model),
    ("diffn", diffn_model),
];

/// Two random constraints over shared variables: the first model's
/// variables, with the second model's leading variables mapped onto them.
fn conjunction(rng: &mut Rng) -> Model {
    let a = (MODELS[rng.index(MODELS.len())].1)(rng);
    let b = (MODELS[rng.index(MODELS.len())].1)(rng);
    let shared = rng.index(a.domains.len().min(b.domains.len()) + 1);
    let mut domains = a.domains.clone();
    let mut map_b: Vec<usize> = Vec::new();
    for (k, d) in b.domains.iter().enumerate() {
        if k < shared {
            // Shared variable: intersect the domains (keep the first's if empty).
            let common: Vec<i64> = domains[k]
                .iter()
                .copied()
                .filter(|v| d.contains(v))
                .collect();
            if !common.is_empty() {
                domains[k] = common;
            }
            map_b.push(k);
        } else {
            domains.push(d.clone());
            map_b.push(domains.len() - 1);
        }
    }
    let na = a.domains.len();
    let label = format!("{} AND {} (shared {shared})", a.label, b.label);
    let (ha, hb, pa, pb) = (a.holds, b.holds, a.post, b.post);
    let mb = map_b.clone();
    Model {
        domains,
        holds: Box::new(move |x, d| {
            let xb: Vec<i64> = mb.iter().map(|&i| x[i]).collect();
            let db: Vec<Vec<i64>> = mb.iter().map(|&i| d[i].clone()).collect();
            ha(&x[..na], &d[..na]) && hb(&xb, &db)
        }),
        post: Box::new(move |v| {
            let vb: Vec<IntVarId> = map_b.iter().map(|&i| v[i]).collect();
            let mut out = pa(&v[..na]);
            out.extend(pb(&vb));
            out
        }),
        label,
    }
}

impl Model {
    fn solutions(&self) -> Option<Vec<Vec<i64>>> {
        let mut total = 1usize;
        for d in &self.domains {
            total = total.checked_mul(d.len())?;
            if total > 20_000 {
                return None;
            }
        }
        let mut out = Vec::new();
        let mut x = vec![0; self.domains.len()];
        self.enumerate(0, &mut x, &mut out);
        Some(out)
    }

    fn enumerate(&self, k: usize, x: &mut [i64], out: &mut Vec<Vec<i64>>) {
        if k == x.len() {
            if (self.holds)(x, &self.domains) {
                out.push(x.to_vec());
            }
            return;
        }
        for &v in &self.domains[k] {
            x[k] = v;
            self.enumerate(k + 1, x, out);
        }
    }

    fn engine(&self) -> (CpSatEngine, Vec<IntVarId>) {
        let mut engine = CpSatEngine::new();
        let vars: Vec<IntVarId> = self
            .domains
            .iter()
            .enumerate()
            .map(|(i, d)| engine.new_int_var(Domain::from_values(d), Some(&format!("x{i}"))))
            .collect();
        for c in (self.post)(&vars) {
            engine.add_constraint(c);
        }
        (engine, vars)
    }

    /// All solutions by solve-and-block, projected on the model variables.
    fn enumerate_with_engine(&self, limit: usize) -> Result<Vec<Vec<i64>>, String> {
        let (mut engine, vars) = self.engine();
        let mut found: Vec<Vec<i64>> = Vec::new();
        loop {
            match engine.solve() {
                CpSolveResult::Sat(assignment) => {
                    let x: Vec<i64> = vars
                        .iter()
                        .map(|&v| {
                            assignment
                                .iter()
                                .find(|(w, _)| *w == v)
                                .expect("assigned")
                                .1
                        })
                        .collect();
                    if !(self.holds)(&x, &self.domains) {
                        return Err(format!("engine returned a non-solution {x:?}"));
                    }
                    if found.contains(&x) {
                        return Err(format!("engine returned {x:?} twice"));
                    }
                    found.push(x.clone());
                    if found.len() > limit {
                        return Err("more solutions than brute force".into());
                    }
                    let projected: Vec<(IntVarId, i64)> =
                        vars.iter().copied().zip(x.iter().copied()).collect();
                    engine.block_assignment(&projected);
                }
                CpSolveResult::Unsat => return Ok(found),
                CpSolveResult::Unknown => return Err("Unknown on a tiny model".into()),
            }
        }
    }

    /// Optimum of `weights . x` by the incremental bound-tightening loop,
    /// with a SAT-only probe of the bound after the first solution.
    fn optimise_with_engine(&self, weights: &[i64], minimize: bool) -> Result<Option<i64>, String> {
        let (mut engine, vars) = self.engine();
        let span: i64 = self
            .domains
            .iter()
            .zip(weights)
            .map(|(d, w)| (d[0] * w).abs().max((d[d.len() - 1] * w).abs()))
            .sum::<i64>()
            + 1;
        let obj = engine.new_int_var(Domain::new(-span, span), Some("obj"));
        let mut coeffs = weights.to_vec();
        coeffs.push(-1);
        let mut all = vars.clone();
        all.push(obj);
        engine.add_constraint(Constraint::LinearEq {
            coeffs,
            vars: all,
            rhs: 0,
        });
        engine.set_objective(obj, minimize);
        let truth = self
            .solutions()
            .expect("small")
            .iter()
            .map(|x| dot(weights, x))
            .reduce(|a, b| if minimize { a.min(b) } else { a.max(b) });
        let mut best: Option<i64> = None;
        for _ in 0..500 {
            match engine.solve() {
                CpSolveResult::Sat(assignment) => {
                    let value_of = |v: IntVarId| {
                        assignment
                            .iter()
                            .find(|(w, _)| *w == v)
                            .expect("assigned")
                            .1
                    };
                    let x: Vec<i64> = vars.iter().map(|&v| value_of(v)).collect();
                    if !(self.holds)(&x, &self.domains) {
                        return Err(format!("engine returned a non-solution {x:?}"));
                    }
                    let value = value_of(obj);
                    if value != dot(weights, &x) {
                        return Err(format!("objective {value} for {x:?}"));
                    }
                    if best.is_none() {
                        let bound = engine.binary_probe_lower_bound(
                            obj,
                            value,
                            minimize,
                            8,
                            Duration::from_secs(5),
                        );
                        let t = truth.expect("a solution exists");
                        let wrong = if minimize { bound > t } else { bound < t };
                        if wrong {
                            return Err(format!("probed bound {bound} passes the optimum {t}"));
                        }
                    }
                    best = Some(value);
                    if minimize {
                        engine.add_upper_bound(obj, value - 1);
                    } else {
                        engine.add_lower_bound(obj, value + 1);
                    }
                }
                CpSolveResult::Unsat => {
                    return if best == truth {
                        Ok(best)
                    } else {
                        Err(format!("optimum {best:?}, brute force {truth:?}"))
                    };
                }
                CpSolveResult::Unknown => return Err("Unknown on a tiny model".into()),
            }
        }
        Err("optimisation did not converge".into())
    }
}

fn check_model(seed: u64, name: &str, model: &Model, rng: &mut Rng) {
    let Some(truth) = model.solutions() else {
        return;
    };
    let mut found = model
        .enumerate_with_engine(truth.len())
        .unwrap_or_else(|e| {
            panic!(
                "{name} seed {seed}: {} {:?}: {e}",
                model.label, model.domains
            )
        });
    found.sort();
    assert_eq!(
        found.len(),
        truth.len(),
        "{name} seed {seed}: {} {:?}: engine enumerates {} solutions, brute force {} \
         (missing: {:?})",
        model.label,
        model.domains,
        found.len(),
        truth.len(),
        truth
            .iter()
            .filter(|x| !found.contains(x))
            .collect::<Vec<_>>()
    );
    if truth.is_empty() {
        return;
    }
    let weights: Vec<i64> = model.domains.iter().map(|_| rng.range(-3, 3)).collect();
    let minimize = rng.chance(50);
    if let Err(e) = model.optimise_with_engine(&weights, minimize) {
        panic!(
            "{name} seed {seed}: {} {:?}, weights {weights:?}, minimize {minimize}: {e}",
            model.label, model.domains
        );
    }
}

fn check_family(name: &str, generate: fn(&mut Rng) -> Model, seeds: u64) {
    for seed in 1..=seeds {
        let mut rng = Rng::from_seed(seed);
        let model = generate(&mut rng);
        check_model(seed, name, &model, &mut rng);
    }
}

#[test]
fn test_every_constraint_enumerates_and_optimises_like_brute_force() {
    for &(name, generate) in MODELS {
        check_family(name, generate, 150);
    }
}

#[test]
fn test_cumulative_enumerates_and_optimises_like_brute_force() {
    check_family("cumulative", cumulative_model, 600);
}

#[test]
fn test_constraint_pairs_enumerate_and_optimise_like_brute_force() {
    check_family("conjunction", conjunction, 600);
}

// ------------------------------------------------- regressions (2026-11-18)

fn check_fixed(name: &str, model: &Model) {
    check_model(0, name, model, &mut Rng::from_seed(1));
}

/// `cumulative([si, sj], [1, 5], [1, 1], 1)`, si in 0..10, sj in 0..8:
/// 57 schedules. The backward explanation left out the blocking task, and
/// enumeration lost `si = 10, sj = 5` (56 found).
#[test]
fn test_cumulative_enumerates_every_schedule() {
    let model = Model {
        domains: vec![
            (0..=10).collect(),
            (0..=8).collect(),
            vec![1],
            vec![5],
            vec![1],
        ],
        holds: Box::new(|x, _| cumulative_holds(&x[..2], &[x[2], x[3]], &[x[4], x[4]], 1)),
        post: Box::new(|v| {
            vec![Constraint::Cumulative {
                starts: v[..2].to_vec(),
                durations: vec![v[2], v[3]],
                demands: vec![v[4], v[4]],
                capacity: 1,
            }]
        }),
        label: "cumulative 3min".into(),
    };
    assert_eq!(model.solutions().map(|s| s.len()), Some(57));
    check_fixed("cumulative", &model);
}
