// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An irrelevant array leaf must not hide a scalar refutation in the same
//! authored conjunction. The requested native proof remains mandatory.

use ay_dpll::api::{Solver, SolverConfig, Sort};
use std::time::Duration;

fn solve(retained_source: bool, pin: i64, negated: bool, disjunctive: bool) -> Solver {
    let mut solver = Solver::try_new_with_smtlib_logic_and_config(
        "QF_ALIA",
        SolverConfig::default().with_timeout(Duration::from_secs(5)),
    )
    .expect("solver");
    solver.set_produce_proofs(true);
    let a = solver.try_declare_const("a", Sort::Bool).unwrap();
    let b = solver.try_declare_const("b", Sort::Bool).unwrap();
    let c = solver.try_declare_const("c", Sort::Bool).unwrap();
    let d = solver.try_declare_const("d", Sort::Bool).unwrap();
    let x = solver.try_declare_const("x", Sort::Int).unwrap();
    let memory = solver
        .try_declare_const("memory", Sort::array(Sort::Int, Sort::Int))
        .unwrap();
    let index = solver.try_declare_const("index", Sort::Int).unwrap();
    let zero = solver.int_const(0);
    let minus_one = solver.int_const(-1);
    let is_zero = solver.try_eq(x, zero).unwrap();
    let b_is_zero = solver.try_eq(b, is_zero).unwrap();
    let both = solver.try_and(a, b).unwrap();
    let c_is_both = solver.try_eq(c, both).unwrap();
    let not_c = solver.try_not(c).unwrap();
    let d_is_not_c = solver.try_eq(d, not_c).unwrap();
    let scalar = solver
        .try_and_many(&[a, d, b_is_zero, c_is_both, d_is_not_c])
        .unwrap();
    let read = solver.try_select(memory, index).unwrap();
    let array_leaf = solver.try_eq(read, minus_one).unwrap();
    let root = if disjunctive {
        solver.try_or(scalar, array_leaf).unwrap()
    } else {
        solver.try_and(scalar, array_leaf).unwrap()
    };
    let root = if negated {
        solver.try_not(root).unwrap()
    } else {
        root
    };
    let value = solver.int_const(pin);
    let pin = solver.try_eq(x, value).unwrap();
    for assertion in [root, pin] {
        if retained_source {
            let source = format!(
                "(assert {})",
                solver.format_term_checked(assertion).unwrap()
            );
            solver
                .try_assert_term_with_source(assertion, &source)
                .unwrap();
        } else {
            solver.try_assert_term(assertion).unwrap();
        }
    }
    let details = solver.check_sat_with_details();
    if negated || disjunctive || value != zero {
        assert!(details.result.is_sat(), "satisfiable neighbor: {details:?}");
    } else {
        assert!(
            details.result.is_unsat(),
            "array leaf must not hide the proof: {details:?}"
        );
        assert!(details.result.was_unsat_strictly_verified());
        assert!(solver.last_proof().is_some());
        assert!(solver
            .last_strict_proof_quality()
            .is_some_and(|r| r.is_ok_and(|q| q.is_complete())));
    }
    solver
}

#[test]
fn native_mixed_conjunction_has_a_checked_refutation() {
    solve(false, 0, false, false);
}

#[test]
fn retained_source_mixed_conjunction_has_a_checked_refutation() {
    solve(true, 0, false, false);
}

#[test]
fn satisfiable_pin_neighbor_is_not_refuted() {
    solve(true, 1, false, false);
}

#[test]
fn disjunction_does_not_authorize_its_scalar_branch() {
    solve(true, 0, false, true);
}

#[test]
fn negative_conjunction_does_not_authorize_its_scalar_children() {
    solve(true, 0, true, false);
}

const NESTED_MIXED_SMT: &str = r#"
(set-option :produce-proofs true)
(set-option :timeout 5000)
(set-logic QF_ALIA)
(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(declare-const d Bool)
(declare-const x Int)
(declare-const memory (Array Int Int))
(declare-const index Int)
(assert (and (and a d) (and (= b (= x 0))
    (and (= c (and a b)) (= d (not c)) (= (select memory index) (- 1))))))
(assert (= x 0))
(check-sat)
"#;

#[test]
fn nested_authored_conjunction_has_a_checked_scope_bound_refutation() {
    use ay_proof::{AletheRule, ProofStep};

    let mut executor = ay_dpll::Executor::new();
    let results = executor
        .execute_all(&ay_frontend::parse(NESTED_MIXED_SMT).unwrap())
        .unwrap();
    assert_eq!(results.last().unwrap().to_string(), "unsat");
    let proof = executor
        .last_proof()
        .expect("requested proof must be retained");
    let quality = ay_proof::check_proof_strict(proof, executor.terms()).unwrap();
    assert!(quality.is_complete());
    assert_eq!(quality.trust_count, 0);
    assert_eq!(quality.hole_count, 0);

    // The new transport is a real checked projection, not a new assumption.
    // Re-indexing one projection must be rejected by the unchanged checker.
    let mut forged = proof.clone();
    let projection = forged
        .steps
        .iter_mut()
        .find_map(|step| match step {
            ProofStep::Step {
                rule: rule @ AletheRule::AndPos(_),
                ..
            } => Some(rule),
            _ => None,
        })
        .expect("the mixed root requires a derived scalar conjunct");
    *projection = AletheRule::AndPos(u32::MAX);
    assert!(ay_proof::check_proof_strict(&forged, executor.terms()).is_err());

    let scope: Vec<_> = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Assume(root) => Some(*root),
            _ => None,
        })
        .collect();
    let child = proof
        .steps
        .iter()
        .find_map(|step| match step {
            ProofStep::Step {
                rule: AletheRule::AndPos(_),
                clause,
                ..
            } if clause.len() == 2 && !scope.contains(&clause[1]) => Some(clause[1]),
            _ => None,
        })
        .expect("a projected child is not an authored root");
    let mut foreign = proof.clone();
    let assumption = foreign
        .steps
        .iter_mut()
        .find_map(|step| match step {
            ProofStep::Assume(root) => Some(root),
            _ => None,
        })
        .unwrap();
    *assumption = child;
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&foreign, &scope).is_err());
}

#[test]
fn nested_authored_satisfiable_neighbor_is_not_refuted() {
    let input = NESTED_MIXED_SMT.replace("(assert (= x 0))", "(assert (= x 1))");
    let mut executor = ay_dpll::Executor::new();
    let results = executor
        .execute_all(&ay_frontend::parse(&input).unwrap())
        .unwrap();
    assert_eq!(results.last().unwrap().to_string(), "sat");
    assert!(executor.last_proof().is_none());
}
