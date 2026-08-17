// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::parser::parse_qdimacs;
use crate::QuantifierBlock;

#[test]
fn test_decision_order_omits_variables_absent_from_matrix() {
    let formula = QbfFormula::new(
        5,
        vec![QuantifierBlock::exists(vec![1, 2])],
        vec![vec![Literal::positive(Variable::new(2))]],
    );
    let solver = QbfSolver::new(formula);

    assert_eq!(solver.decision_order, vec![2]);
}

#[test]
fn tautological_universal_matrix_finishes_with_default_budget() {
    const VARIABLES: u32 = 20;
    let quantified: Vec<u32> = (1..=VARIABLES).collect();
    let clauses = quantified
        .iter()
        .map(|&variable| {
            vec![
                Literal::positive(Variable::new(variable)),
                Literal::negative(Variable::new(variable)),
            ]
        })
        .collect();
    let formula = QbfFormula::new(
        VARIABLES as usize,
        vec![QuantifierBlock::forall(quantified)],
        clauses,
    );
    let mut solver = QbfSolver::new(formula);

    assert!(matches!(solver.solve(), QbfResult::Sat(_)));
    assert_eq!(solver.stats().decisions, 0);
}

#[test]
fn unused_outer_universals_do_not_consume_default_budget() {
    const UNUSED: u32 = 20;
    let witness = UNUSED + 1;
    let formula = QbfFormula::new(
        witness as usize,
        vec![
            QuantifierBlock::forall((1..=UNUSED).collect()),
            QuantifierBlock::exists(vec![witness]),
        ],
        vec![vec![Literal::positive(Variable::new(witness))]],
    );
    let mut solver = QbfSolver::new(formula);

    assert!(matches!(solver.solve(), QbfResult::Sat(_)));
    assert_eq!(solver.stats().decisions, 1);
}

#[test]
fn test_empty_matrix_clause_is_unsat() {
    let formula = parse_qdimacs("p cnf 0 1\n0\n").unwrap();
    let mut solver = QbfSolver::new(formula);

    assert!(matches!(solver.solve(), QbfResult::Unsat(_)));
}

#[test]
fn test_native_malformed_prefix_is_canonicalized_without_panicking() {
    let x = Literal::positive(Variable::new(1));
    let formula = QbfFormula::new(
        1,
        vec![
            QuantifierBlock::exists(vec![0, 1, 2]),
            QuantifierBlock::forall(vec![1]),
        ],
        vec![vec![x]],
    );
    assert_eq!(
        formula.prefix,
        vec![QuantifierBlock::exists(vec![1])],
        "the first valid occurrence defines the canonical prefix"
    );
    let mut solver = QbfSolver::new(formula);

    assert!(matches!(solver.solve(), QbfResult::Sat(_)));
}

#[test]
fn test_solver_recanonicalizes_publicly_mutated_prefix() {
    let x = Literal::positive(Variable::new(1));
    let mut formula = QbfFormula::new(1, vec![QuantifierBlock::exists(vec![1])], vec![vec![x]]);
    formula.prefix = vec![
        QuantifierBlock::forall(vec![1]),
        QuantifierBlock::exists(vec![1]),
    ];

    let mut solver = QbfSolver::new(formula);
    assert!(matches!(solver.solve(), QbfResult::Unsat(_)));
}

#[test]
fn test_native_out_of_range_and_zero_literals_fail_closed() {
    let valid = Literal::positive(Variable::new(1));
    for invalid in [
        Literal::negative(Variable::new(2)),
        Literal::positive(Variable::new(0)),
    ] {
        let formula = QbfFormula::new(
            1,
            vec![QuantifierBlock::exists(vec![1])],
            vec![vec![valid, invalid]],
        );
        let mut solver = QbfSolver::new(formula);
        assert_eq!(
            solver.solve(),
            QbfResult::Unknown,
            "invalid native literal {invalid:?} must not reach watch indexing"
        );
    }
}

#[test]
fn test_exact_qdpll_uses_heap_stack_for_deep_prefix() {
    const DEPTH: u32 = 50_000;
    let variables: Vec<u32> = (1..=DEPTH).collect();
    let formula = QbfFormula::new(
        DEPTH as usize,
        vec![QuantifierBlock::exists(variables)],
        vec![vec![Literal::positive(Variable::new(DEPTH))]],
    );
    let mut solver = QbfSolver::new(formula);

    assert!(matches!(
        solver.solve_with_limit(u64::from(DEPTH)),
        QbfResult::Sat(_)
    ));
}

#[test]
fn test_matrix_literal_work_is_bounded_independently_of_nodes() {
    const CLAUSE_LEN: u32 = 4_096;
    let variables: Vec<u32> = (1..=CLAUSE_LEN).collect();
    let clause: Vec<Literal> = variables
        .iter()
        .copied()
        .map(|variable| Literal::positive(Variable::new(variable)))
        .collect();
    let formula = QbfFormula::new(
        CLAUSE_LEN as usize,
        vec![QuantifierBlock::exists(variables)],
        vec![clause],
    );
    let mut solver = QbfSolver::new(formula);

    assert_eq!(solver.solve_with_limit(1), QbfResult::Unknown);
    assert_eq!(
        solver.stats().decisions,
        0,
        "literal work must stop the initial matrix scan before a node is consumed"
    );
}

#[test]
fn test_small_qbf_formulas_match_truth_table() {
    fn matrix_value(clauses: &[Vec<Literal>], assignment: &[bool]) -> bool {
        clauses.iter().all(|clause| {
            clause.iter().any(|literal| {
                assignment[literal.variable().id() as usize - 1] == literal.is_positive()
            })
        })
    }

    fn truth_value(
        clauses: &[Vec<Literal>],
        existential_mask: usize,
        variable: usize,
        assignment: &mut [bool],
    ) -> bool {
        if variable == assignment.len() {
            return matrix_value(clauses, assignment);
        }

        assignment[variable] = false;
        let when_false = truth_value(clauses, existential_mask, variable + 1, assignment);
        assignment[variable] = true;
        let when_true = truth_value(clauses, existential_mask, variable + 1, assignment);
        if existential_mask & (1 << variable) != 0 {
            when_false || when_true
        } else {
            when_false && when_true
        }
    }

    for num_vars in 1usize..=3 {
        let mut clause_universe = Vec::new();
        for encoding in 1usize..3usize.pow(num_vars as u32) {
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

        let mut matrices = vec![Vec::<Vec<Literal>>::new()];
        for first in 0..clause_universe.len() {
            matrices.push(vec![clause_universe[first].clone()]);
            for second in first + 1..clause_universe.len() {
                matrices.push(vec![
                    clause_universe[first].clone(),
                    clause_universe[second].clone(),
                ]);
                for third in second + 1..clause_universe.len() {
                    matrices.push(vec![
                        clause_universe[first].clone(),
                        clause_universe[second].clone(),
                        clause_universe[third].clone(),
                    ]);
                }
            }
        }

        for existential_mask in 0usize..1 << num_vars {
            let prefix: Vec<_> = (0..num_vars)
                .map(|index| {
                    let variable = index as u32 + 1;
                    if existential_mask & (1 << index) != 0 {
                        QuantifierBlock::exists(vec![variable])
                    } else {
                        QuantifierBlock::forall(vec![variable])
                    }
                })
                .collect();

            for clauses in &matrices {
                let expected =
                    truth_value(clauses, existential_mask, 0, &mut vec![false; num_vars]);
                let formula = QbfFormula::new(num_vars, prefix.clone(), clauses.clone());
                let result = QbfSolver::new(formula).solve();
                assert!(
                    matches!(
                        (expected, &result),
                        (true, QbfResult::Sat(_))
                            | (false, QbfResult::Unsat(_))
                    ),
                    "truth-table disagreement: vars={num_vars}, existential_mask={existential_mask:#b}, clauses={clauses:?}, expected={expected}, result={result:?}"
                );
            }
        }
    }
}

#[test]
fn test_simple_sat_qbf() {
    // ∃x. x
    // This is SAT: just set x = true
    let input = "p cnf 1 1\ne 1 0\n1 0\n";
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve();
    assert!(matches!(result, QbfResult::Sat(_)));
}

#[test]
fn test_simple_unsat_qbf() {
    // ∃x. (x ∧ ¬x)
    // This is UNSAT
    let input = "p cnf 1 2\ne 1 0\n1 0\n-1 0\n";
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve();
    assert!(matches!(result, QbfResult::Unsat(_)));
}

#[test]
fn test_universal_sat() {
    // ∀x. (x ∨ ¬x)
    // This is SAT (tautology)
    let input = "p cnf 1 1\na 1 0\n1 -1 0\n";
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve();
    assert!(matches!(result, QbfResult::Sat(_)));
}

#[test]
fn test_universal_unsat() {
    // ∀x. x
    // This is UNSAT: when x = false, clause is false
    let input = "p cnf 1 1\na 1 0\n1 0\n";
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve();
    assert!(matches!(result, QbfResult::Unsat(_)));
}

#[test]
fn test_exists_forall_sat() {
    // ∃x∀y. (x ∨ y) ∧ (x ∨ ¬y)
    // SAT: set x = true, then both clauses satisfied regardless of y
    let input = "p cnf 2 2\ne 1 0\na 2 0\n1 2 0\n1 -2 0\n";
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve();
    assert!(matches!(result, QbfResult::Sat(_)));
}

#[test]
fn test_exists_forall_unsat() {
    // ∃x∀y. (x ∨ y) ∧ (¬x ∨ ¬y)
    // UNSAT:
    // - If x = true, adversary sets y = true, second clause false
    // - If x = false, adversary sets y = false, first clause false
    let input = "p cnf 2 2\ne 1 0\na 2 0\n1 2 0\n-1 -2 0\n";
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve();
    assert!(matches!(result, QbfResult::Unsat(_)));
}

#[test]
fn test_forall_exists_sat() {
    // ∀x∃y. (x ∨ y) ∧ (¬x ∨ ¬y)
    // SAT: for any x, set y = ¬x
    // - If x = true, set y = false: (T∨F)∧(F∨T) = T∧T = T
    // - If x = false, set y = true: (F∨T)∧(T∨F) = T∧T = T
    let input = "p cnf 2 2\na 1 0\ne 2 0\n1 2 0\n-1 -2 0\n";
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve();
    assert!(matches!(result, QbfResult::Sat(_)));
}

#[test]
fn test_universal_reduction() {
    // ∃x∀y. (x ∨ y)
    // After universal reduction of y (level 1 >= max_exist 0), clause becomes (x)
    // SAT: set x = true
    let input = "p cnf 2 1\ne 1 0\na 2 0\n1 2 0\n";
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve();
    assert!(matches!(result, QbfResult::Sat(_)));
}

#[test]
fn test_stats() {
    let input = "p cnf 2 2\ne 1 0\na 2 0\n1 2 0\n-1 -2 0\n";
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    solver.solve();
    let stats = solver.stats();
    // Should have some activity
    assert!(stats.decisions > 0 || stats.propagations > 0 || stats.conflicts > 0);
}

#[test]
fn test_three_quantifier_blocks_sat() {
    // ∃x∀y∃z. (x ∨ y ∨ z) ∧ (¬x ∨ ¬y ∨ z) ∧ (x ∨ ¬y ∨ ¬z)
    // SAT: set x = true, z = true
    // For any y:
    //   y=T: (T∨T∨T) ∧ (F∨F∨T) ∧ (T∨F∨F) = T ∧ T ∧ T = T
    //   y=F: (T∨F∨T) ∧ (F∨T∨T) ∧ (T∨T∨F) = T ∧ T ∧ T = T
    let input = r#"
p cnf 3 3
e 1 0
a 2 0
e 3 0
1 2 3 0
-1 -2 3 0
1 -2 -3 0
"#;
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve();
    assert!(matches!(result, QbfResult::Sat(_)));
}

#[test]
fn test_three_quantifier_blocks_unsat() {
    // ∃x∀y∃z. (y) ∧ (¬y)
    // This is UNSAT because for y=T or y=F, one clause fails
    let input = r#"
p cnf 3 2
e 1 0
a 2 0
e 3 0
2 0
-2 0
"#;
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve();
    assert!(matches!(result, QbfResult::Unsat(_)));
}

#[test]
fn test_multiple_existential_per_block() {
    // ∃x₁x₂∀y. (x₁ ∨ x₂ ∨ y) ∧ (x₁ ∨ x₂ ∨ ¬y)
    // SAT: set x₁ = true (or x₂ = true)
    let input = r#"
p cnf 3 2
e 1 2 0
a 3 0
1 2 3 0
1 2 -3 0
"#;
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve();
    assert!(matches!(result, QbfResult::Sat(_)));
}

#[test]
fn test_multiple_universal_per_block() {
    // ∃x∀y₁y₂. (x ∨ y₁ ∨ y₂) ∧ (x ∨ y₁ ∨ ¬y₂) ∧ (x ∨ ¬y₁ ∨ y₂) ∧ (x ∨ ¬y₁ ∨ ¬y₂)
    // SAT: set x = true (satisfies all clauses regardless of y₁, y₂)
    let input = r#"
p cnf 3 4
e 1 0
a 2 3 0
1 2 3 0
1 2 -3 0
1 -2 3 0
1 -2 -3 0
"#;
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve();
    assert!(matches!(result, QbfResult::Sat(_)));
}

#[test]
fn test_forall_exists_unsat_dependency() {
    // ∀x∃y. (x ∨ y) ∧ (¬x ∨ y) ∧ (x ∨ ¬y) ∧ (¬x ∨ ¬y)
    // UNSAT: y cannot satisfy all clauses for all x
    // x=T: need y for (¬x∨y), need ¬y for (x∨¬y) - contradiction
    // x=F: need y for (x∨y), need ¬y for (¬x∨¬y) - contradiction
    let input = r#"
p cnf 2 4
a 1 0
e 2 0
1 2 0
-1 2 0
1 -2 0
-1 -2 0
"#;
    let formula = parse_qdimacs(input).unwrap();
    let mut solver = QbfSolver::new(formula);
    let result = solver.solve_with_limit(100);
    assert!(
        matches!(result, QbfResult::Unsat(_)),
        "Expected Unsat, got {result:?}"
    );
}

mod learned_database;

#[test]
fn oversized_native_formula_fails_closed_without_dense_allocation() {
    let formula = QbfFormula::new(usize::MAX, Vec::new(), Vec::new());
    assert_eq!(formula.num_vars, usize::MAX);
    assert_eq!(formula.var_level(u32::MAX), 0);
    assert!(formula.is_existential(u32::MAX));

    let mut solver = QbfSolver::new(formula);
    assert_eq!(solver.solve_with_limit(1), QbfResult::Unknown);
}
