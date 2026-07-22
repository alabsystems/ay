// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::common::{assert_model_satisfies, verify_model};
use ay_sat::{parse_dimacs, Literal, SatResult, Solver, Variable};
use ntest::timeout;

/// Test a simple satisfiable formula: (x1 OR x2) AND (NOT x1 OR x2) AND (x1 OR NOT x2)
/// Solution: x1 = true, x2 = true
#[test]
#[timeout(1_000)]
fn test_simple_sat() {
    let dimacs = r"
c Simple SAT formula
p cnf 2 3
1 2 0
-1 2 0
1 -2 0
";
    let formula = parse_dimacs(dimacs).expect("Failed to parse DIMACS");
    assert_eq!(formula.num_vars, 2);
    assert_eq!(formula.clauses.len(), 3);

    let mut solver = formula.into_solver();
    let result = solver.solve().into_inner();

    match result {
        SatResult::Sat(model) => {
            assert_eq!(model.len(), 2);
            assert!(model[0] || model[1]);
            assert!(!model[0] || model[1]);
            assert!(model[0] || !model[1]);
        }
        SatResult::Unsat(_) => panic!("Formula should be satisfiable"),
        SatResult::Unknown => panic!("Got Unknown for simple SAT formula"),
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

/// Test an unsatisfiable formula: x1 AND NOT x1
#[test]
#[timeout(1_000)]
fn test_simple_unsat() {
    let dimacs = r"
c Simple UNSAT formula: x AND NOT x
p cnf 1 2
1 0
-1 0
";
    let formula = parse_dimacs(dimacs).expect("Failed to parse DIMACS");
    let mut solver = formula.into_solver();
    let result = solver.solve().into_inner();

    match result {
        SatResult::Sat(_) => panic!("Formula should be unsatisfiable"),
        SatResult::Unsat(_) => {}
        SatResult::Unknown => panic!("Got Unknown for simple UNSAT formula"),
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

/// Test empty clause (immediately UNSAT)
#[test]
#[timeout(1_000)]
fn test_empty_clause() {
    let mut solver = Solver::new(2);
    let success = solver.add_clause(vec![]);
    assert!(!success, "Adding empty clause should fail");
}

/// Test unit clause propagation setup
#[test]
#[timeout(1_000)]
fn test_unit_clause() {
    let dimacs = r"
p cnf 3 3
1 0
2 0
-3 0
";
    let formula = parse_dimacs(dimacs).expect("Failed to parse DIMACS");
    let solver = formula.into_solver();

    assert_eq!(solver.value(Variable::new(0)), None);
    assert_eq!(solver.value(Variable::new(1)), None);
    assert_eq!(solver.value(Variable::new(2)), None);
}

/// Test larger formula (3-SAT random)
#[test]
#[timeout(1_000)]
fn test_3sat_formula() {
    let dimacs = r"
c Random 3-SAT formula
p cnf 5 10
1 2 3 0
-1 2 4 0
1 -2 5 0
-1 -2 -3 0
2 3 -4 0
-2 3 5 0
1 -3 4 0
-1 3 -5 0
2 -3 -4 0
-2 -3 5 0
";
    let formula = parse_dimacs(dimacs).expect("Failed to parse DIMACS");
    assert_eq!(formula.num_vars, 5);
    assert_eq!(formula.clauses.len(), 10);

    let clauses = formula.clauses.clone();
    let mut solver = formula.into_solver();
    let result = solver.solve().into_inner();

    match result {
        SatResult::Sat(model) => {
            assert_eq!(model.len(), 5);
            assert_model_satisfies(&clauses, &model, "test_3sat_formula");
        }
        SatResult::Unsat(_) => panic!("This formula should be satisfiable"),
        SatResult::Unknown => panic!("Got Unknown for larger SAT formula"),
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

mod parser_tests {
    use ay_sat::{parse_dimacs, DimacsError};
    use ntest::timeout;

    #[test]
    #[timeout(1_000)]
    fn test_missing_problem_line() {
        let dimacs = "1 2 0\n-1 0\n";
        let result = parse_dimacs(dimacs);
        assert!(matches!(result, Err(DimacsError::MissingProblemLine)));
    }

    #[test]
    #[timeout(1_000)]
    fn test_invalid_problem_line() {
        let dimacs = "p sat 3 2\n1 2 0\n";
        let result = parse_dimacs(dimacs);
        assert!(matches!(
            result,
            Err(DimacsError::InvalidProblemLine { .. })
        ));
    }

    #[test]
    #[timeout(1_000)]
    fn test_variable_out_of_range() {
        let dimacs = "p cnf 2 1\n1 2 3 0\n";
        let result = parse_dimacs(dimacs);
        assert!(matches!(
            result,
            Err(DimacsError::VariableOutOfRange { var: 3, max: 2, .. })
        ));
    }

    #[test]
    #[timeout(1_000)]
    fn test_comments_ignored() {
        let dimacs = r"
c This is a comment
c Another comment
p cnf 2 1
c Comment between
1 2 0
c Final comment
";
        let formula = parse_dimacs(dimacs).expect("Should parse with comments");
        assert_eq!(formula.num_vars, 2);
        assert_eq!(formula.clauses.len(), 1);
    }
}

#[test]
#[timeout(1_000)]
fn test_verify_model_helper() {
    let clauses = vec![vec![
        Literal::positive(Variable::new(0)),
        Literal::negative(Variable::new(1)),
    ]];

    assert!(verify_model(&clauses, &[true, true]));
    assert!(verify_model(&clauses, &[false, false]));
    assert!(!verify_model(&clauses, &[false, true]));
}

/// Test phase saving improves performance (regression test)
#[test]
#[timeout(2_000)]
fn test_phase_saving_enabled() {
    let dimacs = r"
p cnf 5 10
1 2 3 0
-1 2 4 0
1 -2 5 0
-1 -2 -3 0
2 3 -4 0
-2 3 5 0
1 -3 4 0
-1 3 -5 0
2 -3 -4 0
-2 -3 5 0
";
    let formula = parse_dimacs(dimacs).expect("Failed to parse");
    let clauses = formula.clauses.clone();
    let mut solver = formula.into_solver();
    let result = solver.solve().into_inner();

    match result {
        SatResult::Sat(model) => {
            assert_eq!(model.len(), 5);
            assert_model_satisfies(&clauses, &model, "test_phase_saving_enabled");
        }
        _ => panic!("Formula should be SAT"),
    }
}
