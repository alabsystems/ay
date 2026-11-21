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
use crate::propagators::soundness_tests::{clamp_i64, dot_wide, End, Place, Rng};
use std::cell::Cell;

thread_local! {
    /// A clause-DB byte limit every engine of this thread gets (see
    /// [`CpSatEngine::set_clause_db_limit_for_tests`]); tests run on their
    /// own threads, so it never leaks into another test.
    static CLAUSE_DB_LIMIT: Cell<Option<usize>> = const { Cell::new(None) };
    /// What the engines of this thread did: reductions, and solves that
    /// reduced without making a conflict (only the extension loop's
    /// clause-DB limit check reduces there; a conflict-scheduled reduction
    /// needs a conflict).
    static REDUCTIONS: Cell<(u64, u64)> = const { Cell::new((0, 0)) };
}

/// `engine.solve()`, counting the SAT core's reductions on the way.
fn counted_solve(engine: &mut CpSatEngine) -> CpSolveResult {
    let (conflicts, reductions) = (engine.sat.num_conflicts(), engine.sat.num_reductions());
    let result = engine.solve();
    // A solve may start by resetting both counters (an incremental search
    // reset): then they count this solve alone.
    let since = |before: u64, after: u64| after.checked_sub(before).unwrap_or(after);
    let reduced = since(reductions, engine.sat.num_reductions());
    let without_conflict =
        u64::from(reduced > 0 && since(conflicts, engine.sat.num_conflicts()) == 0);
    REDUCTIONS.with(|r| {
        let (total, between) = r.get();
        r.set((total + reduced, between + without_conflict));
    });
    result
}

/// The constraint's meaning on values, given the root domains (circuit and
/// inverse number their nodes from the domains).
type Holds = Box<dyn Fn(&[i64], &[Vec<i64>]) -> bool>;
type Post = Box<dyn Fn(&[IntVarId]) -> Vec<Constraint>>;
/// A generator of random small models, at the given end of i64 (see
/// [`Place`]; with `End::Zero` the models are the ones drawn before the
/// ends were added: same seeds, same values).
pub(super) type Generate = fn(&mut Rng, End) -> Model;

/// A model over variables `x0..xn` with explicit root domains.
pub(super) struct Model {
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

/// `c . x` without overflow.
fn dot(c: &[i64], x: &[i64]) -> i128 {
    dot_wide(c, x)
}

/// The end opposite to `end` (`End::Zero` stays).
fn opposite(end: End) -> End {
    match end {
        End::Zero => End::Zero,
        End::Min => End::Max,
        End::Max => End::Min,
    }
}

fn alldifferent_model(rng: &mut Rng, end: End) -> Model {
    let n = small(rng, 2, 5);
    let place = Place::new(end, 0, 4);
    Model {
        domains: (0..n).map(|_| place.domain(rng, 0, 4)).collect(),
        holds: Box::new(|x, _| distinct(x)),
        post: Box::new(|v| vec![Constraint::AllDifferent(v.to_vec())]),
        label: "alldifferent".into(),
    }
}

fn linear_model(rng: &mut Rng, end: End) -> Model {
    let n = small(rng, 1, 3);
    let coeffs: Vec<i64> = (0..n).map(|_| rng.range(-3, 3)).collect();
    let place = Place::new(end, -3, 4);
    let total: i128 = coeffs.iter().map(|&c| i128::from(c)).sum();
    let rhs = clamp_i64(i128::from(rng.range(-6, 6)) + total * place.shift());
    let kind = rng.index(3);
    let label = format!("linear kind {kind} {coeffs:?} . x ~ {rhs}");
    let c = coeffs.clone();
    Model {
        domains: (0..n).map(|_| place.domain(rng, -3, 4)).collect(),
        holds: Box::new(move |x, _| match kind {
            0 => dot(&c, x) <= i128::from(rhs),
            1 => dot(&c, x) == i128::from(rhs),
            _ => dot(&c, x) >= i128::from(rhs),
        }),
        post: Box::new(move |v| {
            let (coeffs, vars) = (coeffs.clone(), v.to_vec());
            vec![match kind {
                0 => Constraint::LinearLe { coeffs, vars, rhs },
                1 => Constraint::LinearEq { coeffs, vars, rhs },
                _ => Constraint::LinearGe { coeffs, vars, rhs },
            }]
        }),
        label,
    }
}

fn linear_ne_model(rng: &mut Rng, end: End) -> Model {
    let n = small(rng, 1, 3);
    let coeffs: Vec<i64> = (0..n).map(|_| rng.range(-3, 3)).collect();
    let place = Place::new(end, -2, 3);
    let total: i128 = coeffs.iter().map(|&c| i128::from(c)).sum();
    let rhs = clamp_i64(i128::from(rng.range(-4, 4)) + total * place.shift());
    let label = format!("linear_ne {coeffs:?} . x != {rhs}");
    let c = coeffs.clone();
    Model {
        domains: (0..n).map(|_| place.domain(rng, -2, 3)).collect(),
        holds: Box::new(move |x, _| dot(&c, x) != i128::from(rhs)),
        post: Box::new(move |v| {
            vec![Constraint::LinearNotEqual {
                coeffs: coeffs.clone(),
                vars: v.to_vec(),
                rhs,
            }]
        }),
        label,
    }
}

fn pairwise_neq_model(rng: &mut Rng, end: End) -> Model {
    let offset = rng.range(-3, 3);
    // Wide domains take the lazy path (checked on complete assignments).
    let wide = rng.chance(30);
    let place_x = Place::new(end, 0, 70);
    // At an end, y sometimes lies at the other end: `x - y` is then far
    // outside i64. (Not with wide domains: without an overlap they take the
    // eager path, and 71 * 71 free assignments only cost time.)
    let place_y = if end != End::Zero && !wide && rng.chance(30) {
        Place::new(opposite(end), 0, 70)
    } else {
        place_x
    };
    let domains = if wide {
        vec![
            (0..=70).map(|v| place_x.at(v)).collect(),
            (0..=70).map(|v| place_y.at(v)).collect::<Vec<i64>>(),
        ]
    } else {
        vec![place_x.domain(rng, 0, 5), place_y.domain(rng, 0, 5)]
    };
    Model {
        domains,
        holds: Box::new(move |x, _| i128::from(x[0]) - i128::from(x[1]) != i128::from(offset)),
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

fn element_model(rng: &mut Rng, end: End) -> Model {
    let len = small(rng, 1, 3);
    let top = i64::try_from(len).expect("small") - 1;
    let mut domains = vec![random_domain(rng, 0, top)];
    let place = Place::new(end, 0, 3);
    domains.extend((0..=len).map(|_| place.domain(rng, 0, 3)));
    // At an end, the index domain is sometimes there too (no position).
    if end != End::Zero && rng.chance(20) {
        domains[0] = Place::new(end, 0, top).domain(rng, 0, top);
    }
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

fn table_model(rng: &mut Rng, end: End) -> Model {
    let n = small(rng, 1, 3);
    let place = Place::new(end, 0, 3);
    let tuples: Vec<Vec<i64>> = (0..rng.range(0, 6))
        .map(|_| (0..n).map(|_| place.range(rng, 0, 3)).collect())
        .collect();
    let t = tuples.clone();
    Model {
        domains: (0..n).map(|_| place.domain(rng, 0, 3)).collect(),
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

/// At no time `t` do the tasks `[s, s + d)` running at `t` demand more than
/// `capacity` (in i128: an end `s + d` may pass `i64::MAX`).
///
/// The load only rises at a start time, so those are the times checked
/// (shared variables can put starts at both ends of i64 at once).
fn cumulative_holds(s: &[i64], d: &[i64], r: &[i64], capacity: i64) -> bool {
    let end = |i: usize| i128::from(s[i]) + i128::from(d[i]);
    (0..s.len()).map(|i| i128::from(s[i])).all(|t| {
        (0..s.len())
            .filter(|&i| i128::from(s[i]) <= t && t < end(i))
            .map(|i| i128::from(r[i]))
            .sum::<i128>()
            <= i128::from(capacity)
    })
}

fn cumulative_model(rng: &mut Rng, end: End) -> Model {
    let n = small(rng, 2, 3);
    let horizon = rng.range(4, 8);
    let capacity = rng.range(1, 3);
    // Start times move to the end; durations and demands stay small, so at
    // `End::Max` a task may run past `i64::MAX`.
    let place = Place::new(end, 0, horizon);
    let mut domains: Vec<Vec<i64>> = (0..n).map(|_| place.domain(rng, 0, horizon)).collect();
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

/// No two tasks `[s, s + d)` overlap (in i128).
fn disjoint(s: &[i64], d: &[i64]) -> bool {
    let end = |i: usize| i128::from(s[i]) + i128::from(d[i]);
    (0..s.len()).all(|i| {
        ((i + 1)..s.len()).all(|j| end(i) <= i128::from(s[j]) || end(j) <= i128::from(s[i]))
    })
}

fn disjunctive_model(rng: &mut Rng, end: End) -> Model {
    let n = small(rng, 2, 3);
    let horizon = rng.range(5, 9);
    let durations: Vec<i64> = (0..n).map(|_| rng.range(1, 4)).collect();
    let place = Place::new(end, 0, horizon);
    let d = durations.clone();
    Model {
        domains: (0..n).map(|_| place.domain(rng, 0, horizon)).collect(),
        holds: Box::new(move |s, _| disjoint(s, &d)),
        post: Box::new(move |v| {
            vec![Constraint::Disjunctive {
                starts: v.to_vec(),
                durations: durations.clone(),
            }]
        }),
        label: "disjunctive".into(),
    }
}

/// The smallest value in the domains: the numbering the models below use
/// unless they move it (and the rule `circuit_numbered_by_domains` and
/// `inverse_numbered_by_domains` state).
fn node_base(domains: &[Vec<i64>]) -> i64 {
    domains.iter().map(|d| d[0]).min().unwrap_or(0)
}

/// With `moved`, the numbering is the domains' one moved by -1, 0 or 1
/// (where that is an i64): a successor value may then lie outside the
/// nodes, and a node may be no value of any domain.
fn numbering(rng: &mut Rng, domains: &[Vec<i64>], moved: bool) -> i64 {
    let base = node_base(domains);
    if moved {
        base.checked_add(rng.range(-1, 1)).unwrap_or(base)
    } else {
        base
    }
}

/// Successor `x[i]` (nodes `base..`): one cycle through all nodes.
fn is_circuit(x: &[i64], base: i64) -> bool {
    let n = x.len();
    let mut seen = vec![false; n];
    let mut node = 0usize;
    for _ in 0..n {
        if seen[node] {
            return false;
        }
        seen[node] = true;
        match usize::try_from(i128::from(x[node]) - i128::from(base)) {
            Ok(next) if next < n => node = next,
            _ => return false,
        }
    }
    node == 0 && seen.iter().all(|&s| s)
}

/// Template window of successor values for `n` nodes: `0..n`, or at an end
/// sometimes `1..n` for two nodes or more (one value short of a
/// permutation; against `i64::MAX` the node numbering then runs past it).
fn node_window(rng: &mut Rng, end: End, n: usize) -> (i64, i64) {
    let top = i64::try_from(n).expect("small") - 1;
    if end != End::Zero && n >= 2 && rng.chance(25) {
        (1, top)
    } else {
        (0, top)
    }
}

fn circuit_model(rng: &mut Rng, end: End) -> Model {
    circuit_numbered(rng, end, false)
}

fn circuit_moved_model(rng: &mut Rng, end: End) -> Model {
    circuit_numbered(rng, end, true)
}

fn circuit_numbered(rng: &mut Rng, end: End, moved: bool) -> Model {
    let n = small(rng, 2, 5);
    let (lo, top) = node_window(rng, end, n);
    let place = Place::new(end, 0, top);
    // Keep x[0]'s domain the whole window, as the generator always has.
    let mut domains = vec![(lo..=top).map(|v| place.at(v)).collect::<Vec<i64>>()];
    for _ in 1..n {
        let mut d = place.domain(rng, lo, top);
        if rng.chance(50) {
            d = (lo..=top).map(|v| place.at(v)).collect();
        }
        domains.push(d);
    }
    let base = numbering(rng, &domains, moved);
    Model {
        domains,
        holds: Box::new(move |x, _| is_circuit(x, base)),
        post: Box::new(move |v| {
            vec![Constraint::Circuit {
                succ: v.to_vec(),
                base,
            }]
        }),
        label: format!("circuit {n} from {base}"),
    }
}

/// `x[i] = j` (numbered from `bx`) exactly when `y[j] = i` (from `by`).
fn is_inverse(x: &[i64], y: &[i64], bx: i64, by: i64) -> bool {
    let n = x.len();
    let one_way = |x: &[i64], y: &[i64], bx: i64, by: i64| {
        (0..n).all(|i| {
            usize::try_from(i128::from(x[i]) - i128::from(bx))
                .ok()
                .and_then(|j| y.get(j))
                .is_some_and(|&yj| i128::from(yj) - i128::from(by) == i as i128)
        })
    };
    y.len() == n && one_way(x, y, bx, by) && one_way(y, x, by, bx)
}

fn inverse_model(rng: &mut Rng, end: End) -> Model {
    inverse_numbered(rng, end, false)
}

fn inverse_moved_model(rng: &mut Rng, end: End) -> Model {
    inverse_numbered(rng, end, true)
}

fn inverse_numbered(rng: &mut Rng, end: End, moved: bool) -> Model {
    let n = small(rng, 1, 4);
    let (lo, top) = node_window(rng, end, n);
    // At an end, y is numbered at either end or around zero.
    let place_x = Place::new(end, 0, top);
    let place_y = if end == End::Zero {
        place_x
    } else {
        Place::new([End::Zero, End::Min, End::Max][rng.index(3)], 0, top)
    };
    let mut domains = Vec::new();
    for k in 0..2 * n {
        let place = if k < n { place_x } else { place_y };
        // Each array's first variable keeps the whole window.
        if k % n == 0 || rng.chance(50) {
            domains.push((lo..=top).map(|v| place.at(v)).collect());
        } else {
            domains.push(place.domain(rng, lo, top));
        }
    }
    let base_x = numbering(rng, &domains[..n], moved);
    let base_y = numbering(rng, &domains[n..], moved);
    Model {
        domains,
        holds: Box::new(move |v, _| {
            let (x, y) = v.split_at(n);
            is_inverse(x, y, base_x, base_y)
        }),
        post: Box::new(move |v| {
            vec![Constraint::Inverse {
                x: v[..n].to_vec(),
                y: v[n..].to_vec(),
                base_x,
                base_y,
            }]
        }),
        label: format!("inverse {n} from {base_x}, {base_y}"),
    }
}

fn bool_clause_model(rng: &mut Rng, end: End) -> Model {
    let n = small(rng, 1, 4);
    let positive: Vec<bool> = (0..n).map(|_| rng.chance(50)).collect();
    let p = positive.clone();
    let place = Place::new(end, 0, 1);
    Model {
        domains: (0..n).map(|_| place.domain(rng, 0, 1)).collect(),
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

fn abs_model(rng: &mut Rng, end: End) -> Model {
    // At an end, the argument lies there and the result against i64::MAX,
    // where `|arg|` lands (`|i64::MIN|` is past it).
    let place_result = Place::new(if end == End::Zero { end } else { End::Max }, -2, 5);
    let place_arg = Place::new(end, -5, 5);
    Model {
        domains: vec![
            place_result.domain(rng, -2, 5),
            place_arg.domain(rng, -5, 5),
        ],
        holds: Box::new(|x, _| i128::from(x[0]) == i128::from(x[1]).abs()),
        post: Box::new(|v| {
            vec![Constraint::Abs {
                result: v[0],
                arg: v[1],
            }]
        }),
        label: "abs".into(),
    }
}

fn min_max_model(rng: &mut Rng, end: End) -> Model {
    let n = small(rng, 1, 3);
    let maximum = rng.chance(50);
    let place = Place::new(end, -2, 4);
    Model {
        domains: (0..=n).map(|_| place.domain(rng, -2, 4)).collect(),
        holds: Box::new(move |x, _| {
            let args = &x[1..];
            let want = if maximum {
                args.iter().max()
            } else {
                args.iter().min()
            };
            want == Some(&x[0])
        }),
        post: Box::new(move |v| {
            let (result, args) = (v[0], v[1..].to_vec());
            vec![if maximum {
                Constraint::Maximum { result, args }
            } else {
                Constraint::Minimum { result, args }
            }]
        }),
        label: format!("min/max, maximum {maximum}"),
    }
}

fn diffn_model(rng: &mut Rng, end: End) -> Model {
    let n = small(rng, 2, 2);
    // Positions move to the end; sizes stay small, so at `End::Max` a
    // rectangle may reach past `i64::MAX`.
    let place = Place::new(end, 0, 3);
    // Per rectangle: x, y, dx, dy.
    let mut domains = Vec::new();
    for _ in 0..n {
        domains.push(place.domain(rng, 0, 3));
        domains.push(place.domain(rng, 0, 3));
        domains.push(random_domain(rng, 0, 2));
        domains.push(random_domain(rng, 0, 2));
    }
    Model {
        domains,
        holds: Box::new(move |v, _| {
            let r = |i: usize| {
                (
                    i128::from(v[4 * i]),
                    i128::from(v[4 * i + 1]),
                    i128::from(v[4 * i + 2]),
                    i128::from(v[4 * i + 3]),
                )
            };
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
/// `x * y = r` or `x div y = r` (truncating, `y != 0`).
fn arithmetic_model(rng: &mut Rng, divide: bool) -> Model {
    let domains = vec![
        random_domain(rng, -5, 6),
        random_domain(rng, -4, 5),
        if divide {
            random_domain(rng, -6, 6)
        } else {
            random_domain(rng, -15, 20)
        },
    ];
    Model {
        domains,
        holds: Box::new(move |x, _| {
            let (a, b, r) = (i128::from(x[0]), i128::from(x[1]), i128::from(x[2]));
            if divide {
                b != 0 && a / b == r
            } else {
                a * b == r
            }
        }),
        post: Box::new(move |v| {
            let (x, y, result) = (v[0], v[1], v[2]);
            vec![if divide {
                Constraint::Div { x, y, result }
            } else {
                Constraint::Times { x, y, result }
            }]
        }),
        label: if divide { "div" } else { "times" }.into(),
    }
}

// The two arithmetic families are not moved to the ends of i64: a product
// of two values there is not representable, so `end` is ignored and the
// instances are the same at every end.
fn times_model(rng: &mut Rng, _end: End) -> Model {
    arithmetic_model(rng, false)
}

fn div_model(rng: &mut Rng, _end: End) -> Model {
    arithmetic_model(rng, true)
}

pub(super) const MODELS: &[(&str, Generate)] = &[
    ("alldifferent", alldifferent_model),
    ("linear", linear_model),
    ("linear_ne", linear_ne_model),
    ("pairwise_neq", pairwise_neq_model),
    ("element", element_model),
    ("table", table_model),
    ("cumulative", cumulative_model),
    ("disjunctive", disjunctive_model),
    ("circuit", circuit_model),
    ("circuit_moved", circuit_moved_model),
    ("inverse", inverse_model),
    ("inverse_moved", inverse_moved_model),
    ("bool_clause", bool_clause_model),
    ("abs", abs_model),
    ("min_max", min_max_model),
    ("diffn", diffn_model),
    ("times", times_model),
    ("div", div_model),
];

/// Two random constraints over shared variables: the first model's
/// variables, with the second model's leading variables mapped onto them.
fn conjunction(rng: &mut Rng, end: End) -> Model {
    let a = (MODELS[rng.index(MODELS.len())].1)(rng, end);
    let b = (MODELS[rng.index(MODELS.len())].1)(rng, end);
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
        self.solutions_within(20_000)
    }

    /// Brute force over at most `cap` assignments.
    fn solutions_within(&self, cap: usize) -> Option<Vec<Vec<i64>>> {
        let mut total = 1usize;
        for d in &self.domains {
            total = total.checked_mul(d.len())?;
            if total > cap {
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
        if let Some(bytes) = CLAUSE_DB_LIMIT.get() {
            engine.set_clause_db_limit_for_tests(bytes);
        }
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
            match counted_solve(&mut engine) {
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
        // Objective domain: `[-span, span]` as always, or, at the ends of
        // i64 where that is not representable, the exact range of
        // `weights . x`; neither representable: no objective to test.
        let terms = || {
            self.domains.iter().zip(weights).map(|(d, &w)| {
                let a = i128::from(d[0]) * i128::from(w);
                let b = i128::from(d[d.len() - 1]) * i128::from(w);
                (a.min(b), a.max(b))
            })
        };
        let span: i128 = terms().map(|(a, b)| a.abs().max(b.abs())).sum::<i128>() + 1;
        let (lo, hi) = terms().fold((0i128, 0i128), |(lo, hi), (a, b)| (lo + a, hi + b));
        // (A domain spans at most i64::MAX values.)
        let domain = |lo: i128, hi: i128| {
            Domain::try_new(i64::try_from(lo).ok()?, i64::try_from(hi).ok()?).ok()
        };
        let Some(objective_domain) = domain(-span, span).or_else(|| domain(lo, hi)) else {
            return Ok(None);
        };
        let (mut engine, vars) = self.engine();
        let obj = engine.new_int_var(objective_domain, Some("obj"));
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
            .solutions_within(BIG_MODEL_CAP)
            .expect("small")
            .iter()
            .map(|x| i64::try_from(dot(weights, x)).expect("inside the objective domain"))
            .reduce(|a, b| if minimize { a.min(b) } else { a.max(b) });
        let mut best: Option<i64> = None;
        for _ in 0..500 {
            match counted_solve(&mut engine) {
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
                    if i128::from(value) != dot(weights, &x) {
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
                    // At the end of the objective's i64 range there is no
                    // better value to ask for.
                    let next = if minimize {
                        value.checked_sub(1)
                    } else {
                        value.checked_add(1)
                    };
                    let Some(next) = next else {
                        return if best == truth {
                            Ok(best)
                        } else {
                            Err(format!("optimum {best:?}, brute force {truth:?}"))
                        };
                    };
                    if minimize {
                        engine.add_upper_bound(obj, next);
                    } else {
                        engine.add_lower_bound(obj, next);
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

fn check_model(seed: u64, name: &str, model: &Model, rng: &mut Rng, end: End) {
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
    // At an end, one variable is the objective (any weighted sum of two
    // values there leaves i64).
    let weights: Vec<i64> = if end == End::Zero {
        model.domains.iter().map(|_| rng.range(-3, 3)).collect()
    } else {
        let k = rng.index(model.domains.len());
        (0..model.domains.len())
            .map(|i| i64::from(i == k))
            .collect()
    };
    let minimize = rng.chance(50);
    if let Err(e) = model.optimise_with_engine(&weights, minimize) {
        panic!(
            "{name} seed {seed}: {} {:?}, weights {weights:?}, minimize {minimize}: {e}",
            model.label, model.domains
        );
    }
}

pub(super) fn check_family(name: &str, generate: Generate, seeds: u64) {
    check_family_at(name, generate, seeds, End::Zero);
}

fn check_family_at(name: &str, generate: Generate, seeds: u64, end: End) {
    for seed in 1..=seeds {
        let mut rng = Rng::from_seed(seed);
        let model = generate(&mut rng, end);
        if std::env::var_os("AY_CP_BRUTE_FORCE_TRACE").is_some() {
            eprintln!(
                "{name} at {end:?} seed {seed}: {} {:?}",
                model.label, model.domains
            );
        }
        check_model(seed, &format!("{name} at {end:?}"), &model, &mut rng, end);
    }
}

#[test]
fn test_every_constraint_enumerates_and_optimises_like_brute_force() {
    for &(name, generate) in MODELS {
        check_family(name, generate, 150);
    }
}

/// Every constraint with its values against `i64::MIN` and against
/// `i64::MAX`, alone and in pairs: no lost or wrong solution, the right
/// optimum, and no panic on an overflow (debug builds) or wrap (release
/// builds) in an encoder, a propagator or the debug validator.
#[test]
fn test_every_constraint_at_the_ends_of_i64() {
    let mut failures = Vec::new();
    let families = MODELS
        .iter()
        .copied()
        .chain(std::iter::once(("conjunction", conjunction as Generate)));
    for (name, generate) in families {
        for end in End::BOTH {
            // A panic is a failure of this family at this end; the others
            // still run.
            if std::panic::catch_unwind(|| check_family_at(name, generate, 80, end)).is_err() {
                failures.push(format!("{name} at {end:?} (see stderr)"));
            }
        }
    }
    assert!(failures.is_empty(), "failed: {failures:?}");
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
    check_model(0, name, model, &mut Rng::from_seed(1), End::Zero);
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

/// Successors over nodes 1..4 where node 1 cannot take value 1 (it would
/// succeed itself): the base was read from the first successor's lower
/// bound (2), and a node in last position could point anywhere, so
/// `[2, 1, 4, 3]` (two subtours) passed as a circuit. (The numbering is
/// stated since 2026-11-19.)
#[test]
fn test_circuit_numbering_and_last_position() {
    let model = Model {
        domains: vec![
            vec![2, 3, 4],
            (1..=4).collect(),
            (1..=4).collect(),
            (1..=4).collect(),
        ],
        holds: Box::new(|x, _| is_circuit(x, 1)),
        post: Box::new(|v| {
            vec![Constraint::Circuit {
                succ: v.to_vec(),
                base: 1,
            }]
        }),
        label: "circuit 4".into(),
    };
    assert_eq!(model.solutions().map(|s| s.len()), Some(6));
    check_fixed("circuit", &model);
}

/// `y[1]` cannot be 3 and `y[3]` can only be 3. The channeling clauses
/// for a pair `x[i] = j` where `y[j]` cannot take `i` were skipped, which
/// left `x[i] = j` unconstrained: the engine returned `x = [3, 2, 0, 1]`
/// with `y = [2, 0, 1, 3]` (random seed 52).
#[test]
fn test_inverse_forbids_pairs_the_other_side_cannot_take() {
    let full: Vec<i64> = (0..=3).collect();
    let model = Model {
        domains: vec![
            full.clone(),
            full.clone(),
            full.clone(),
            full.clone(),
            full.clone(),
            vec![0, 1, 2],
            full,
            vec![3],
        ],
        holds: Box::new(|v, _| {
            let (x, y) = v.split_at(4);
            (0..4).all(|i| y[usize::try_from(x[i]).expect("in range")] == i as i64)
        }),
        post: Box::new(|v| {
            vec![Constraint::Inverse {
                x: v[..4].to_vec(),
                y: v[4..].to_vec(),
                base_x: 0,
                base_y: 0,
            }]
        }),
        label: "inverse 4".into(),
    };
    assert_eq!(model.solutions().map(|s| s.len()), Some(6));
    check_fixed("inverse", &model);
}

/// A fixed result had no clause tying it to the arguments: `2 = max([1])`
/// and `2 = min([4])` were accepted.
#[test]
fn test_min_max_with_a_fixed_result() {
    for maximum in [true, false] {
        let model = Model {
            domains: vec![vec![2], if maximum { vec![0, 1] } else { vec![4, 5] }],
            holds: Box::new(move |x, _| x[0] == x[1]),
            post: Box::new(move |v| {
                let (result, args) = (v[0], vec![v[1]]);
                vec![if maximum {
                    Constraint::Maximum { result, args }
                } else {
                    Constraint::Minimum { result, args }
                }]
            }),
            label: format!("maximum {maximum}"),
        };
        assert_eq!(model.solutions().map(|s| s.len()), Some(0));
        check_fixed("min_max", &model);
    }
}

// ------------------------------- clause-DB limit reductions (2026-11-19)
//
// A memory budget gives the SAT core a clause-DB byte limit, and the
// extension CDCL loop reduces whenever it is exceeded, between conflicts as
// well as after them (AY-OTHER-6). A reduction deletes propagator
// explanations the engine then has to derive again. The budget's floor (the
// compiled model plus 64 MB) keeps every model above out of reach of that
// path, so these tests install a 1-byte limit directly and compare every
// answer with brute force again.

/// Largest assignment space the fixed models below enumerate by brute force.
const BIG_MODEL_CAP: usize = 1_000_000;

/// Runs `body` with a 1-byte clause-DB limit on every engine it builds and
/// returns (reductions, solves that reduced without a conflict).
fn with_tiny_clause_db_limit(body: impl FnOnce()) -> (u64, u64) {
    CLAUSE_DB_LIMIT.set(Some(1));
    REDUCTIONS.set((0, 0));
    body();
    CLAUSE_DB_LIMIT.set(None);
    let (reductions, without_conflict) = REDUCTIONS.get();
    eprintln!("{reductions} reductions, {without_conflict} solves reduced without a conflict");
    (reductions, without_conflict)
}

/// `n` queens, one per column: `x[i]` is the row of the queen in column `i`.
fn queens(n: usize, first_column: Vec<i64>) -> Model {
    let rows: Vec<i64> = (0..i64::try_from(n).expect("small")).collect();
    let mut domains = vec![rows.clone(); n];
    domains[0] = first_column;
    Model {
        domains,
        holds: Box::new(|x, _| {
            (0..x.len()).all(|i| {
                ((i + 1)..x.len()).all(|j| {
                    let gap = i64::try_from(j - i).expect("small");
                    x[i] != x[j] && (x[i] - x[j]).abs() != gap
                })
            })
        }),
        post: Box::new(|v| {
            let mut out = Vec::new();
            for i in 0..v.len() {
                for j in (i + 1)..v.len() {
                    let gap = i64::try_from(j - i).expect("small");
                    for offset in [0, gap, -gap] {
                        out.push(Constraint::PairwiseNeq {
                            x: v[i],
                            y: v[j],
                            offset,
                        });
                    }
                }
            }
            out
        }),
        label: format!("{n} queens"),
    }
}

/// Enumeration and both optimisation directions against brute force.
fn check_big(model: &Model, weights: &[i64], solutions: usize) {
    let truth = model.solutions_within(BIG_MODEL_CAP).expect("within cap");
    assert_eq!(truth.len(), solutions, "{}: brute force", model.label);
    let mut found = model
        .enumerate_with_engine(truth.len())
        .unwrap_or_else(|e| panic!("{}: {e}", model.label));
    found.sort();
    assert_eq!(found, truth, "{}: enumeration", model.label);
    if truth.is_empty() {
        return;
    }
    for minimize in [true, false] {
        model
            .optimise_with_engine(weights, minimize)
            .unwrap_or_else(|e| panic!("{}, minimize {minimize}: {e}", model.label));
    }
}

/// Every harness family, with the clause-DB limit reductions firing: the
/// same solution sets and optima as brute force.
#[test]
fn test_clause_db_limit_reductions_keep_every_family_like_brute_force() {
    let (reductions, without_conflict) = with_tiny_clause_db_limit(|| {
        for &(name, generate) in MODELS {
            check_family(name, generate, 150);
        }
        check_family("cumulative", cumulative_model, 200);
        check_family("conjunction", conjunction, 300);
    });
    assert!(reductions > 0, "no reduction under a 1-byte limit");
    assert!(
        without_conflict > 0,
        "no solve reduced between conflicts ({reductions} reductions)"
    );
}

/// An UNSAT search (no queen in a corner of a 6 x 6 board can be part of a
/// solution) and a 7-queens enumeration (40 solutions) and optimisation,
/// with the clause-DB limit reductions firing.
#[test]
fn test_clause_db_limit_reductions_keep_unsat_and_optima() {
    let (reductions, without_conflict) = with_tiny_clause_db_limit(|| {
        check_big(&queens(6, vec![0, 5]), &[], 0);
        check_big(&queens(7, (0..7).collect()), &[3, -1, 2, 0, -2, 1, -3], 40);
    });
    assert!(reductions > 0, "no reduction under a 1-byte limit");
    assert!(without_conflict > 0, "no solve reduced between conflicts");
}

/// Control for the counters above: without a limit nothing reduces between
/// conflicts.
#[test]
fn test_no_clause_db_limit_no_reduction_between_conflicts() {
    REDUCTIONS.set((0, 0));
    check_family("linear", linear_model, 50);
    check_big(&queens(6, vec![0, 5]), &[], 0);
    assert_eq!(REDUCTIONS.get().1, 0);
}
