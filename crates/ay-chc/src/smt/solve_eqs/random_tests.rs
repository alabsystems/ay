// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exhaustive-grid soundness check of `solve_eqs` on random Bool/Real
//! formulas: every grid point that satisfies the input satisfies the
//! residual (so a refuted residual never hides a model — no false UNSAT),
//! and every grid point of the residual's variables that satisfies it
//! completes to a model of the input (model reconstruction).

use super::*;
use num_bigint::BigInt;

const REALS: [&str; 4] = ["x0", "x1", "x2", "x3"];
const BOOLS: [&str; 2] = ["b0", "b1"];
const GRID: [i64; 4] = [-1, 0, 1, 2];

/// Deterministic generator (fixed seed; no flaky reruns).
struct Lcg(u64);

impl Lcg {
    fn below(&mut self, n: u64) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (self.0 >> 33) % n
    }
}

fn rvar(r: &mut Lcg) -> ChcExpr {
    let name = REALS[r.below(REALS.len() as u64) as usize];
    ChcExpr::var(ChcVar::new(name, ChcSort::Real))
}

fn bvar(r: &mut Lcg) -> ChcExpr {
    let name = BOOLS[r.below(BOOLS.len() as u64) as usize];
    ChcExpr::var(ChcVar::new(name, ChcSort::Bool))
}

fn constant(r: &mut Lcg) -> ChcExpr {
    ChcExpr::Real(r.below(4) as i64 - 1, 1 + r.below(2) as i64)
}

fn term(r: &mut Lcg, depth: u32) -> ChcExpr {
    match r.below(6) {
        0 => constant(r),
        1 | 2 => rvar(r),
        3 => ChcExpr::add(rvar(r), constant(r)),
        4 if depth > 0 => {
            let d = depth - 1;
            ChcExpr::ite(atom(r, d), term(r, d), term(r, d))
        }
        _ => ChcExpr::mul(constant(r), rvar(r)),
    }
}

fn atom(r: &mut Lcg, depth: u32) -> ChcExpr {
    match r.below(6) {
        0 | 1 => ChcExpr::eq(term(r, depth), term(r, depth)),
        2 => ChcExpr::le(term(r, depth), term(r, depth)),
        3 => ChcExpr::lt(term(r, depth), term(r, depth)),
        4 => bvar(r),
        _ => ChcExpr::eq(bvar(r), ChcExpr::le(term(r, depth), term(r, depth))),
    }
}

fn formula(r: &mut Lcg, depth: u32) -> ChcExpr {
    if depth == 0 || r.below(3) == 0 {
        return atom(r, 1);
    }
    let d = depth - 1;
    match r.below(5) {
        0 => ChcExpr::and(formula(r, d), formula(r, d)),
        1 => ChcExpr::or(formula(r, d), formula(r, d)),
        2 => ChcExpr::not(formula(r, d)),
        3 => ChcExpr::ite(formula(r, d), formula(r, d), formula(r, d)),
        _ => ChcExpr::implies(formula(r, d), formula(r, d)),
    }
}

/// A conjunction rich in top-level definitions, so the pass has work to do.
fn query(r: &mut Lcg) -> ChcExpr {
    let parts = 2 + r.below(5);
    ChcExpr::and_all((0..parts).map(|_| match r.below(6) {
        0 | 1 => ChcExpr::eq(rvar(r), term(r, 1)),
        2 => bvar(r),
        3 => ChcExpr::not(bvar(r)),
        _ => formula(r, 3),
    }))
}

fn grid_models() -> Vec<FxHashMap<String, SmtValue>> {
    let mut out = Vec::new();
    let points = GRID.len().pow(REALS.len() as u32) << BOOLS.len();
    for mut code in 0..points {
        let mut m = FxHashMap::default();
        for b in BOOLS {
            m.insert(b.to_string(), SmtValue::Bool((code & 1) == 1));
            code >>= 1;
        }
        for x in REALS {
            let v = GRID[code % GRID.len()];
            code /= GRID.len();
            m.insert(
                x.to_string(),
                SmtValue::Real(BigRational::from_integer(BigInt::from(v))),
            );
        }
        out.push(m);
    }
    out
}

fn holds(e: &ChcExpr, m: &FxHashMap<String, SmtValue>) -> Option<bool> {
    match crate::expr::evaluate_expr(e, m)? {
        SmtValue::Bool(b) => Some(b),
        _ => None,
    }
}

#[test]
fn residual_is_implied_and_models_complete_on_random_formulas() {
    let mut rng = Lcg(0x5eed_2026_0930);
    let grid = grid_models();
    let mut solved_count = 0usize;
    for case in 0..800 {
        let f = query(&mut rng);
        let reach = if case % 2 == 0 {
            Reach::Full
        } else {
            Reach::Plain
        };
        let Some(solved) = solve_eqs_with(&f, &FxHashSet::default(), reach) else {
            continue;
        };
        solved_count += 1;
        let eliminated: FxHashSet<String> =
            solved.defs.iter().map(|(v, _)| v.name.clone()).collect();
        for m in &grid {
            // Input model ⇒ residual model (never a false refutation).
            if holds(&f, m) == Some(true) {
                assert_eq!(
                    holds(&solved.residual, m),
                    Some(true),
                    "case {case}: {f}\nresidual {}\nmodel {m:?}",
                    solved.residual
                );
            }
            // Residual model on the surviving variables ⇒ completed model of
            // the input.
            let mut kept: FxHashMap<String, SmtValue> = m
                .iter()
                .filter(|(k, _)| !eliminated.contains(*k))
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect();
            if holds(&solved.residual, &kept) == Some(true) {
                assert!(solved.complete_model(&f.vars(), &mut kept), "case {case}");
                assert_eq!(
                    holds(&f, &kept),
                    Some(true),
                    "case {case}: {f}\nresidual {}\ncompleted {kept:?}",
                    solved.residual
                );
            }
        }
    }
    assert!(
        solved_count > 200,
        "only {solved_count} cases exercised the pass"
    );
}
