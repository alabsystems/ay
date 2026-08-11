// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::types::{PbLit, PbTerm};

fn term(coeff: i128, var: u32) -> PbTerm {
    PbTerm {
        coeff,
        lits: vec![PbLit {
            var,
            negated: false,
        }],
    }
}

fn neg_term(coeff: i128, var: u32) -> PbTerm {
    PbTerm {
        coeff,
        lits: vec![PbLit { var, negated: true }],
    }
}

fn ge(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
    PbConstraint {
        terms,
        rel: PbRel::Ge,
        rhs,
    }
}

fn eq(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
    PbConstraint {
        terms,
        rel: PbRel::Eq,
        rhs,
    }
}

/// Builds an OPT instance from raw parts.
fn inst(num_vars: u32, constraints: Vec<PbConstraint>) -> PbInstance {
    PbInstance {
        num_vars,
        num_constraints: constraints.len() as u32,
        constraints,
        objective: None,
    }
}

fn obj(terms: Vec<PbTerm>) -> PbObjective {
    PbObjective { terms }
}

/// Runs the solver with an infinite budget and a no-op improve sink.
fn run(instance: &PbInstance, objective: &PbObjective) -> Option<PbSolution> {
    let never = || false;
    let mut sink = |_v: i128, _m: &[bool]| {};
    try_market_split_exact(instance, objective, &never, &mut sink)
}

/// Brute-force reference: min objective over all `2^n` assignments satisfying
/// EVERY constraint (returns `None` when infeasible).
fn brute(instance: &PbInstance, objective: &PbObjective) -> Option<i128> {
    let n = instance.num_vars as usize;
    assert!(n <= 20, "brute force only for small n");
    let mut best: Option<i128> = None;
    for bits in 0u64..(1u64 << n) {
        let assign: Vec<bool> = (0..n).map(|i| (bits >> i) & 1 == 1).collect();
        if crate::eval::verify_all_constraints(&instance.constraints, &assign) {
            let o = crate::solver::eval_objective_exact(objective, &assign).unwrap();
            best = Some(best.map_or(o, |b| b.min(o)));
        }
    }
    best
}

#[test]
fn market_split_pair_unsat_is_proved() {
    // Two equalities encoded as complementary Ge pairs over x2..x4 that cannot
    // both hold: x2+x3 = 2 (both true) AND x3+x4 = 0 (both false) forces x3
    // both true and false -> infeasible. Plus a forced x1 = 0 (min x1).
    let cons = vec![
        // x1 <= 0
        ge(vec![term(-1, 1)], 0),
        // x2 + x3 = 2  (pair)
        ge(vec![term(1, 2), term(1, 3)], 2),
        ge(vec![term(-1, 2), term(-1, 3)], -2),
        // x3 + x4 = 0  (pair)
        ge(vec![term(1, 3), term(1, 4)], 0),
        ge(vec![term(-1, 3), term(-1, 4)], 0),
    ];
    let instance = inst(4, cons);
    let objective = obj(vec![term(1, 1)]);
    let sol = run(&instance, &objective).expect("recognized");
    assert_eq!(sol.status, PbStatus::Unsatisfiable);
    assert_eq!(brute(&instance, &objective), None);
}

#[test]
fn market_split_pair_sat_is_optimum() {
    // x2 + x3 = 1 and x3 + x4 = 1 with min: x2 + x4. Feasible; the optimum sets
    // x3 = 1, x2 = x4 = 0 -> objective 0.
    let cons = vec![
        ge(vec![term(1, 2), term(1, 3)], 1),
        ge(vec![term(-1, 2), term(-1, 3)], -1),
        ge(vec![term(1, 3), term(1, 4)], 1),
        ge(vec![term(-1, 3), term(-1, 4)], -1),
    ];
    let instance = inst(4, cons);
    let objective = obj(vec![term(1, 2), term(1, 4)]);
    let sol = run(&instance, &objective).expect("recognized");
    assert_eq!(sol.status, PbStatus::OptimumFound);
    assert_eq!(sol.objective, Some(0));
    assert_eq!(brute(&instance, &objective), Some(0));
    // Witness must satisfy every original constraint.
    assert!(crate::eval::verify_all_constraints(
        &instance.constraints,
        &sol.assignment
    ));
}

#[test]
fn eq_rows_direct_are_handled() {
    // Same feasible system, but using native `Eq` rows instead of Ge pairs.
    let cons = vec![
        eq(vec![term(1, 1), term(1, 2)], 1),
        eq(vec![term(1, 2), term(1, 3)], 1),
    ];
    let instance = inst(3, cons);
    let objective = obj(vec![term(1, 1), term(1, 3)]);
    let sol = run(&instance, &objective).expect("recognized");
    assert_eq!(sol.status, PbStatus::OptimumFound);
    assert_eq!(sol.objective, brute(&instance, &objective));
    assert!(crate::eval::verify_all_constraints(
        &instance.constraints,
        &sol.assignment
    ));
}

#[test]
fn declines_lone_multivar_inequality() {
    // A multi-variable Ge with no complementary partner: cannot be handled
    // exactly by the equality-only search.
    let cons = vec![
        eq(vec![term(1, 1), term(1, 2)], 1),
        ge(vec![term(1, 2), term(1, 3)], 1), // lone inequality
    ];
    let instance = inst(3, cons);
    let objective = obj(vec![term(1, 1)]);
    assert!(run(&instance, &objective).is_none());
}

#[test]
fn declines_negated_literal() {
    let cons = vec![eq(vec![term(1, 1), neg_term(1, 2)], 1)];
    let instance = inst(2, cons);
    let objective = obj(vec![term(1, 1)]);
    assert!(run(&instance, &objective).is_none());
}

#[test]
fn declines_nonlinear_product() {
    let product = PbTerm {
        coeff: 1,
        lits: vec![
            PbLit {
                var: 1,
                negated: false,
            },
            PbLit {
                var: 2,
                negated: false,
            },
        ],
    };
    let cons = vec![eq(vec![product, term(1, 3)], 1)];
    let instance = inst(3, cons);
    let objective = obj(vec![term(1, 1)]);
    assert!(run(&instance, &objective).is_none());
}

#[test]
fn declines_when_too_many_free_vars() {
    // One equality over MITM_MAX_FREE_VARS + 4 variables: over the size budget.
    let n = (MITM_MAX_FREE_VARS + 4) as u32;
    let terms: Vec<PbTerm> = (1..=n).map(|v| term(1, v)).collect();
    let cons = vec![eq(terms, 3)];
    let instance = inst(n, cons);
    let objective = obj(vec![term(1, 1)]);
    assert!(run(&instance, &objective).is_none());
}

#[test]
fn single_var_contradiction_is_unsat() {
    // x1 >= 1 AND x1 <= 0 is a single-variable contradiction, plus a real
    // equality so the shape is otherwise recognized.
    let cons = vec![
        ge(vec![term(1, 1)], 1),
        ge(vec![term(-1, 1)], 0),
        eq(vec![term(1, 2), term(1, 3)], 1),
    ];
    let instance = inst(3, cons);
    let objective = obj(vec![term(1, 2)]);
    let sol = run(&instance, &objective).expect("recognized");
    assert_eq!(sol.status, PbStatus::Unsatisfiable);
}

#[test]
fn fixed_variable_folds_into_objective_and_rhs() {
    // x1 fixed to 1 (x1 >= 1), appears in an equality and the objective.
    // Equality: x1 + x2 = 2 -> x2 = 1. Objective min: 5 x1 + x2 = 5 + 1 = 6.
    let cons = vec![ge(vec![term(1, 1)], 1), eq(vec![term(1, 1), term(1, 2)], 2)];
    let instance = inst(2, cons);
    let objective = obj(vec![term(5, 1), term(1, 2)]);
    let sol = run(&instance, &objective).expect("recognized");
    assert_eq!(sol.status, PbStatus::OptimumFound);
    assert_eq!(sol.objective, Some(6));
    assert_eq!(sol.assignment, vec![true, true]);
}

#[test]
fn objective_only_variable_is_set_optimally() {
    // x3 appears ONLY in the objective (not in any constraint) with a negative
    // coefficient, so the optimum sets it to 1. Constraint: x1 + x2 = 1.
    // min: x1 - 2 x3. Optimum: x1 = 0, x3 = 1 -> objective -2.
    let cons = vec![eq(vec![term(1, 1), term(1, 2)], 1)];
    let instance = inst(3, cons);
    let objective = obj(vec![term(1, 1), term(-2, 3)]);
    let sol = run(&instance, &objective).expect("recognized");
    assert_eq!(sol.status, PbStatus::OptimumFound);
    assert_eq!(sol.objective, Some(-2));
    assert_eq!(brute(&instance, &objective), Some(-2));
    assert!(crate::eval::verify_all_constraints(
        &instance.constraints,
        &sol.assignment
    ));
    assert!(sol.assignment[2], "objective-only var x3 must be 1");
}

#[test]
fn mitm_matches_brute_force_random() {
    // Deterministic LCG; no external rng dependency.
    let mut state: u64 = 0x1234_5678_9abc_def1;
    let mut next = || {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        state
    };
    let mut checked = 0usize;
    for _ in 0..400 {
        let n = 2 + (next() % 13) as u32; // 2..=14 vars (brute <= 20)
        let m = 1 + (next() % 3) as usize; // 1..=3 equalities
        let mut cons = Vec::new();
        // Optionally plant a solution so ~half are feasible.
        let plant = next() % 2 == 0;
        let planted: Vec<bool> = (0..n).map(|_| next() % 2 == 0).collect();
        for _ in 0..m {
            // dense equality over all n vars with small coeffs
            let coeffs: Vec<i128> = (0..n).map(|_| (next() % 7) as i128 - 3).collect();
            let terms: Vec<PbTerm> = (0..n)
                .filter(|&i| coeffs[i as usize] != 0)
                .map(|i| term(coeffs[i as usize], i + 1))
                .collect();
            if terms.is_empty() {
                continue;
            }
            let rhs = if plant {
                (0..n)
                    .map(|i| coeffs[i as usize] * i128::from(planted[i as usize]))
                    .sum()
            } else {
                (next() % 31) as i128 - 15
            };
            cons.push(eq(terms, rhs));
        }
        if cons.is_empty() {
            continue;
        }
        let objterms: Vec<PbTerm> = (0..n)
            .map(|i| term((next() % 7) as i128 - 3, i + 1))
            .collect();
        let instance = inst(n, cons);
        let objective = obj(objterms);

        let expected = brute(&instance, &objective);
        match run(&instance, &objective) {
            Some(sol) => {
                checked += 1;
                match sol.status {
                    PbStatus::OptimumFound => {
                        assert_eq!(sol.objective, expected, "optimum mismatch n={n} m={m}");
                        assert!(crate::eval::verify_all_constraints(
                            &instance.constraints,
                            &sol.assignment
                        ));
                    }
                    PbStatus::Unsatisfiable => {
                        assert_eq!(expected, None, "claimed UNSAT but feasible n={n} m={m}");
                    }
                    other => panic!("unexpected status {other:?}"),
                }
            }
            None => {
                // Declined (e.g. empty free set): don't constrain, but such
                // cases should be rare here.
            }
        }
    }
    assert!(
        checked > 100,
        "expected many recognized cases, got {checked}"
    );
}

/// Regression (review, 2026-07-13): a header-undercount OPB (`num_vars` less
/// than the max referenced variable) must DECLINE, not index-panic. The parser
/// trusts the declared header verbatim, so a constraint can reference a var
/// beyond `num_vars`; the recognizer must guard every constraint-side index.
#[test]
fn header_undercount_declines_without_panic() {
    // num_vars = 3 but a constraint references var 9 (index 9 >= len 3).
    let i = inst(3, vec![eq(vec![term(1, 0), term(1, 9)], 1)]);
    let o = obj(vec![term(1, 0)]);
    assert!(
        run(&i, &o).is_none(),
        "must decline on out-of-range var, not panic"
    );
    // Also the single-var-bound path and the complementary-Ge path.
    let i2 = inst(2, vec![ge(vec![term(1, 7)], 1)]);
    assert!(run(&i2, &obj(vec![term(1, 0)])).is_none());
}
