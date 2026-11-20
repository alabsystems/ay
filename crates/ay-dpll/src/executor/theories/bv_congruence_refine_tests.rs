// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::TermId;
use ay_frontend::parse;

use super::{violated_congruence_clauses, CongruenceApp, CongruenceArg};
use crate::executor::Executor;

fn bv_arg(lits: &[i32]) -> CongruenceArg {
    CongruenceArg::Lits {
        bool_sorted: false,
        lits: lits.to_vec(),
    }
}

fn app(result: &[i32], args: Vec<CongruenceArg>) -> CongruenceApp {
    CongruenceApp {
        result_bool: false,
        result: result.to_vec(),
        args,
    }
}

/// Value of a DIMACS clause under `model` (variables past its end false).
fn clause_holds(model: &[bool], clause: &[i32]) -> bool {
    clause.iter().any(|&lit| {
        let value = model
            .get(lit.unsigned_abs() as usize - 1)
            .copied()
            .unwrap_or(false);
        if lit > 0 {
            value
        } else {
            !value
        }
    })
}

/// f(a) and f(b), a and b two bits (vars 1-2, 3-4), results one bit (5, 6).
fn two_apps() -> Vec<Vec<CongruenceApp>> {
    vec![vec![
        app(&[5], vec![bv_arg(&[1, 2])]),
        app(&[6], vec![bv_arg(&[3, 4])]),
    ]]
}

#[test]
fn equal_arguments_with_different_results_yield_clauses_the_model_falsifies() {
    // a = b = 01, f(a) = 1, f(b) = 0.
    let model = [true, false, true, false, true, false];
    let mut next_var = 6;
    let clauses = violated_congruence_clauses(&two_apps(), &model, &mut next_var)
        .expect("every literal has a value");
    // The fresh difference variables are 7 and 8; in the extended model
    // they are false (the arguments agree), and some congruence clause fails.
    assert_eq!(next_var, 8);
    let mut extended = model.to_vec();
    extended.extend([false, false]);
    assert!(clauses.iter().any(|c| !clause_holds(&extended, c)));
}

#[test]
fn a_congruent_model_or_different_arguments_yield_nothing() {
    let mut next_var = 6;
    // Equal arguments, equal results.
    let congruent = [true, false, true, false, true, true];
    assert_eq!(
        violated_congruence_clauses(&two_apps(), &congruent, &mut next_var),
        Some(Vec::new())
    );
    // Different arguments, different results: no congruence obligation.
    let different = [true, false, false, false, true, false];
    assert_eq!(
        violated_congruence_clauses(&two_apps(), &different, &mut next_var),
        Some(Vec::new())
    );
    assert_eq!(next_var, 6);
}

#[test]
fn opaque_arguments_relate_only_the_same_term() {
    let groups = vec![vec![
        app(&[1], vec![CongruenceArg::Opaque(TermId(10))]),
        app(&[2], vec![CongruenceArg::Opaque(TermId(11))]),
        app(&[3], vec![CongruenceArg::Opaque(TermId(10))]),
    ]];
    // Results 1, 0, 0: only the first and third share their argument.
    let model = [true, false, false];
    let mut next_var = 3;
    let clauses = violated_congruence_clauses(&groups, &model, &mut next_var).unwrap();
    assert_eq!(clauses, vec![vec![-1, 3], vec![1, -3]]);
}

#[test]
fn a_literal_without_a_model_value_concludes_nothing() {
    let model = [true, false, true];
    let mut next_var = 6;
    assert_eq!(
        violated_congruence_clauses(&two_apps(), &model, &mut next_var),
        None
    );
}

fn solve_with_clause_cap(input: &str, cap: usize) -> Vec<String> {
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.test_euf_bv_congruence_clause_cap = Some(cap);
    exec.execute_all(&commands).unwrap()
}

/// Five applications of `f`; with a clause budget of 0 the BV congruence
/// pass stops after its first pair. The SAT the partial encoding allows
/// used to end `unknown (incomplete)`; the lazy completion checks the model
/// against every pair and publishes the (validated) `sat`.
#[test]
fn a_capped_congruence_pass_is_completed_lazily_to_sat() {
    let input = r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 4)) (_ BitVec 4))
        (declare-fun a () (_ BitVec 4))
        (declare-fun b () (_ BitVec 4))
        (declare-fun c () (_ BitVec 4))
        (declare-fun d () (_ BitVec 4))
        (declare-fun e () (_ BitVec 4))
        (assert (bvule (f a) (f b)))
        (assert (distinct (f c) (f d)))
        (assert (bvult (f e) (f c)))
        (assert (bvule a b))
        (check-sat)
    "#;
    assert_eq!(solve_with_clause_cap(input, 0), vec!["sat"]);
}

/// The same budget on an UNSAT file whose refutation needs a congruence
/// pair the capped pass never emitted: `x1 <= x2 <= x3 <= x1` makes the
/// three arguments equal, so `f(x1) < f(x3)` contradicts congruence. The
/// lazy completion adds the violated pairs until the SAT solver refutes.
#[test]
fn a_capped_congruence_pass_is_completed_lazily_to_unsat() {
    let input = r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 4)) (_ BitVec 4))
        (declare-fun x1 () (_ BitVec 4))
        (declare-fun x2 () (_ BitVec 4))
        (declare-fun x3 () (_ BitVec 4))
        (declare-fun y () (_ BitVec 4))
        (assert (bvule (f y) (f x2)))
        (assert (bvule x1 x2))
        (assert (bvule x2 x3))
        (assert (bvule x3 x1))
        (assert (bvult (f x1) (f x3)))
        (check-sat)
    "#;
    assert_eq!(solve_with_clause_cap(input, 0), vec!["unsat"]);
    // Control: the uncapped pass decides it too.
    let commands = parse(input).unwrap();
    assert_eq!(
        Executor::new().execute_all(&commands).unwrap(),
        vec!["unsat"]
    );
}
