// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Clausal-abstraction engine (`QbfSolver::solve_until`) against brute force.

use super::*;
use std::time::{Duration, Instant};

/// Small deterministic generator (no external dependency).
struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 >> 33
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// A random prenex formula over variables `1..=num_vars` whose quantifier
/// order is the numeric order: variables `1..=free` are free (implicitly
/// outermost existential), the rest are split into consecutive blocks of
/// random quantifier (adjacent blocks may share one). Returns the formula's
/// parts and the brute-force existential mask (bit `v - 1` for variable `v`).
fn random_formula(
    rng: &mut Lcg,
    num_vars: usize,
    free: usize,
) -> (Vec<QuantifierBlock>, Vec<Vec<Literal>>, usize) {
    let mut prefix = Vec::new();
    let mut mask = (1usize << free) - 1;
    let mut var = free + 1;
    while var <= num_vars {
        let width = 1 + rng.below(3) as usize;
        let exists = rng.below(2) == 0;
        let vars: Vec<u32> = (var..=(var + width - 1).min(num_vars))
            .map(|v| v as u32)
            .collect();
        for &v in &vars {
            if exists {
                mask |= 1 << (v - 1);
            }
        }
        var += vars.len();
        prefix.push(if exists {
            QuantifierBlock::exists(vars)
        } else {
            QuantifierBlock::forall(vars)
        });
    }
    let num_clauses = 1 + rng.below(3 * num_vars as u64 + 2) as usize;
    let mut clauses = Vec::with_capacity(num_clauses);
    for _ in 0..num_clauses {
        let len = 1 + rng.below(4) as usize;
        let clause = (0..len)
            .map(|_| {
                let v = Variable::new(1 + rng.below(num_vars as u64) as u32);
                if rng.below(2) == 0 {
                    Literal::positive(v)
                } else {
                    Literal::negative(v)
                }
            })
            .collect();
        clauses.push(clause);
    }
    (prefix, clauses, mask)
}

#[test]
fn abstraction_matches_brute_force_on_random_formulas() {
    let mut rng = Lcg(0x5eed_0b0f_2026_1118);
    // [without free variables, with free variables] x [true, false]
    let mut seen = [[0usize; 2]; 2];
    for round in 0..6000 {
        let num_vars = 1 + rng.below(10) as usize;
        let free = if round % 3 == 0 {
            1 + rng.below(num_vars.min(3) as u64) as usize
        } else {
            0
        };
        let (prefix, clauses, mask) = random_formula(&mut rng, num_vars, free);
        let expected = truth_value(&clauses, mask, 0, &mut vec![false; num_vars])
            .expect("generated variables stay inside the assignment");
        let formula = QbfFormula::new(num_vars, prefix.clone(), clauses.clone());
        let result = QbfSolver::new(formula).solve_until(None);
        assert!(
            matches!(
                (expected, &result),
                (true, QbfResult::Sat(_)) | (false, QbfResult::Unsat(_))
            ),
            "round {round}: expected {expected}, got {result:?}; prefix={prefix:?}, clauses={clauses:?}"
        );
        seen[usize::from(free > 0)][usize::from(!expected)] += 1;
    }
    // Both polarities, with and without free variables, are well covered.
    for row in seen {
        for count in row {
            assert!(count >= 300, "polarity coverage too thin: {seen:?}");
        }
    }
}

#[test]
fn abstraction_matches_truth_table_on_all_small_matrices() {
    // Every matrix of at most three clauses over three variables, under every
    // single-variable-block prefix (the exhaustive table the exact engine is
    // held to).
    let num_vars = 3usize;
    let mut clause_universe = Vec::new();
    for encoding in 1usize..27 {
        let mut rest = encoding;
        let mut clause = Vec::new();
        for variable in 1..=num_vars {
            match rest % 3 {
                1 => clause.push(Literal::positive(Variable::new(variable as u32))),
                2 => clause.push(Literal::negative(Variable::new(variable as u32))),
                _ => {}
            }
            rest /= 3;
        }
        clause_universe.push(clause);
    }
    for existential_mask in 0usize..8 {
        let prefix: Vec<QuantifierBlock> = (0..num_vars)
            .map(|index| {
                let variable = index as u32 + 1;
                if existential_mask & (1 << index) != 0 {
                    QuantifierBlock::exists(vec![variable])
                } else {
                    QuantifierBlock::forall(vec![variable])
                }
            })
            .collect();
        for first in 0..clause_universe.len() {
            for second in first..clause_universe.len() {
                for third in second..clause_universe.len() {
                    let clauses = vec![
                        clause_universe[first].clone(),
                        clause_universe[second].clone(),
                        clause_universe[third].clone(),
                    ];
                    let expected =
                        truth_value(&clauses, existential_mask, 0, &mut [false; 3]).unwrap();
                    let formula = QbfFormula::new(num_vars, prefix.clone(), clauses.clone());
                    let result = QbfSolver::new(formula).solve_until(None);
                    assert!(
                        matches!(
                            (expected, &result),
                            (true, QbfResult::Sat(_)) | (false, QbfResult::Unsat(_))
                        ),
                        "mask={existential_mask:#b}, clauses={clauses:?}, expected={expected}, got {result:?}"
                    );
                }
            }
        }
    }
}

#[test]
fn abstraction_decides_degenerate_matrices() {
    let p = |v: u32| Literal::positive(Variable::new(v));
    let n = |v: u32| Literal::negative(Variable::new(v));
    // Empty matrix: true.
    let formula = QbfFormula::new(2, vec![QuantifierBlock::forall(vec![1, 2])], vec![]);
    assert!(matches!(
        QbfSolver::new(formula).solve_until(None),
        QbfResult::Sat(_)
    ));
    // Empty clause: false.
    let formula = QbfFormula::new(1, vec![QuantifierBlock::exists(vec![1])], vec![vec![]]);
    assert!(matches!(
        QbfSolver::new(formula).solve_until(None),
        QbfResult::Unsat(_)
    ));
    // A purely universal clause: false.
    let formula = QbfFormula::new(
        2,
        vec![
            QuantifierBlock::exists(vec![1]),
            QuantifierBlock::forall(vec![2]),
        ],
        vec![vec![p(1)], vec![n(2)]],
    );
    assert!(matches!(
        QbfSolver::new(formula).solve_until(None),
        QbfResult::Unsat(_)
    ));
    // Only free variables: plain SAT and UNSAT.
    let formula = QbfFormula::new(2, vec![], vec![vec![p(1), p(2)], vec![n(1)]]);
    assert!(matches!(
        QbfSolver::new(formula).solve_until(None),
        QbfResult::Sat(_)
    ));
    let formula = QbfFormula::new(1, vec![], vec![vec![p(1)], vec![n(1)]]);
    assert!(matches!(
        QbfSolver::new(formula).solve_until(None),
        QbfResult::Unsat(_)
    ));
    // Out-of-range literal: fail closed.
    let formula = QbfFormula::new(1, vec![], vec![vec![p(2)]]);
    assert_eq!(
        QbfSolver::new(formula).solve_until(None),
        QbfResult::Unknown
    );
}

/// The existential pigeonhole formula PHP(holes + 1, holes): false, and
/// exponentially hard for resolution.
fn pigeonhole(holes: u32) -> QbfFormula {
    let pigeons = holes + 1;
    let var = |p: u32, h: u32| Variable::new(p * holes + h + 1);
    let mut clauses = Vec::new();
    for p in 0..pigeons {
        clauses.push((0..holes).map(|h| Literal::positive(var(p, h))).collect());
    }
    for h in 0..holes {
        for p in 0..pigeons {
            for q in p + 1..pigeons {
                clauses.push(vec![
                    Literal::negative(var(p, h)),
                    Literal::negative(var(q, h)),
                ]);
            }
        }
    }
    let num_vars = pigeons * holes;
    QbfFormula::new(
        num_vars as usize,
        vec![QuantifierBlock::exists((1..=num_vars).collect())],
        clauses,
    )
}

#[test]
fn abstraction_stops_at_its_deadline() {
    let mut solver = QbfSolver::new(pigeonhole(13));
    let start = Instant::now();
    let result = solver.solve_until(Some(start + Duration::from_millis(200)));
    let elapsed = start.elapsed();
    assert_eq!(
        result,
        QbfResult::Unknown,
        "PHP(14,13) must not finish in 200 ms"
    );
    assert!(
        elapsed >= Duration::from_millis(200),
        "stopped early: {elapsed:?}"
    );
    assert!(
        elapsed < Duration::from_secs(5),
        "overran the deadline: {elapsed:?}"
    );
}

#[test]
fn abstraction_observes_a_passed_deadline_while_preparing() {
    // ∀x. (x) is decided false by universal reduction inside prepare(),
    // before any SAT query. A deadline that has already passed must stop
    // the preparation too, not only the search after it.
    let formula = || {
        QbfFormula::new(
            1,
            vec![QuantifierBlock::forall(vec![1])],
            vec![vec![Literal::positive(Variable::new(1))]],
        )
    };
    assert!(matches!(
        QbfSolver::new(formula()).solve_until(None),
        QbfResult::Unsat(_)
    ));
    let passed = Instant::now();
    assert_eq!(
        QbfSolver::new(formula()).solve_until(Some(passed)),
        QbfResult::Unknown
    );
}

#[test]
fn abstraction_solves_what_the_exact_budget_cannot() {
    // ∀x1..x12 ∃y1..y12 . ∧_i (x_i ↔ y_i): true, with 2^12 universal paths
    // and a matrix of 24 clauses; plus the false variant with one y forced.
    let width = 12u32;
    let x = |i: u32| Variable::new(i + 1);
    let y = |i: u32| Variable::new(width + i + 1);
    let mut clauses = Vec::new();
    for i in 0..width {
        clauses.push(vec![Literal::negative(x(i)), Literal::positive(y(i))]);
        clauses.push(vec![Literal::positive(x(i)), Literal::negative(y(i))]);
    }
    let prefix = vec![
        QuantifierBlock::forall((1..=width).collect()),
        QuantifierBlock::exists((width + 1..=2 * width).collect()),
    ];
    let formula = QbfFormula::new(2 * width as usize, prefix.clone(), clauses.clone());
    assert_eq!(
        QbfSolver::new(formula.clone()).solve_with_limit(1000),
        QbfResult::Unknown
    );
    assert!(matches!(
        QbfSolver::new(formula).solve_until(None),
        QbfResult::Sat(_)
    ));
    clauses.push(vec![Literal::positive(y(5))]);
    let formula = QbfFormula::new(2 * width as usize, prefix, clauses);
    assert!(matches!(
        QbfSolver::new(formula).solve_until(None),
        QbfResult::Unsat(_)
    ));
}
