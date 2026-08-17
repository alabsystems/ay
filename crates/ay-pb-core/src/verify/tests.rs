// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::types::{PbLit, PbTerm};

fn lit(var: u32) -> PbLit {
    PbLit {
        var,
        negated: false,
    }
}
fn term(coeff: i128, var: u32) -> PbTerm {
    PbTerm {
        coeff,
        lits: vec![lit(var)],
    }
}
fn ge(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
    PbConstraint {
        terms,
        rel: PbRel::Ge,
        rhs,
    }
}

fn instance() -> PbInstance {
    // min x1 + x2 + x3  s.t.  x1 + x2 + x3 >= 2   (optimum = 2)
    PbInstance {
        num_vars: 3,
        num_constraints: 1,
        constraints: vec![ge(vec![term(1, 1), term(1, 2), term(1, 3)], 2)],
        objective: Some(PbObjective {
            terms: vec![term(1, 1), term(1, 2), term(1, 3)],
        }),
    }
}

#[test]
fn parses_multi_vline_and_objective() {
    let out = "c hi\no 5\no 2\ns OPTIMUM FOUND\nv x1 -x2\nv x3\n";
    let p = parse_solver_output(out, 3);
    assert_eq!(p.status.as_deref(), Some("OPTIMUM FOUND"));
    assert_eq!(p.objective, Some(2));
    assert!(p.has_model);
    assert_eq!(p.assignment, vec![true, false, true]);
}

#[test]
fn feasible_model_with_matching_objective_passes_without_z3() {
    let inst = instance();
    // x1=1,x2=1,x3=0 -> feasible, objective 2
    let out = parse_solver_output("o 2\ns OPTIMUM FOUND\nv x1 x2 -x3\n", 3);
    let r = verify(&inst, &out, Z3Mode::Off, 10);
    assert_eq!(r.violated_constraints, 0);
    assert_eq!(r.computed_objective, Some(2));
    assert_eq!(r.objective_matches, Some(true));
    assert!(r.ok, "should pass model+objective checks: {:?}", r.messages);
    assert_eq!(
        r.optimality,
        OptimalityCheck::Skipped("z3 check disabled (--no-z3)".to_string())
    );
}

#[test]
fn infeasible_model_fails() {
    let inst = instance();
    // x1=1,x2=0,x3=0 -> sum 1 < 2, infeasible
    let out = parse_solver_output("o 1\ns SATISFIABLE\nv x1 -x2 -x3\n", 3);
    let r = verify(&inst, &out, Z3Mode::Off, 10);
    assert_eq!(r.violated_constraints, 1);
    assert!(!r.ok);
}

#[test]
fn objective_mismatch_fails() {
    let inst = instance();
    // model attains 2 but claims 1
    let out = parse_solver_output("o 1\ns OPTIMUM FOUND\nv x1 x2 -x3\n", 3);
    let r = verify(&inst, &out, Z3Mode::Off, 10);
    assert_eq!(r.objective_matches, Some(false));
    assert!(!r.ok);
}

#[test]
fn smt2_encodes_constraint_and_bound() {
    let inst = instance();
    let smt = emit_smt2_better_than(&inst, inst.objective.as_ref().unwrap(), 2);
    // 0/1 integer encoding (box-bounded), not Bool+ite.
    assert!(smt.contains("(declare-const x1 Int)"));
    assert!(smt.contains("(assert (<= x1 1))"));
    assert!(smt.contains("(set-logic QF_LIA)"));
    assert!(smt.contains("(>= (+ "));
    // objective <= claimed-1 = 1
    assert!(smt.contains("(<= (+ "));
    assert!(smt.contains("(check-sat)"));
}

#[test]
fn int_smt_handles_negatives() {
    assert_eq!(int_smt(5), "5");
    assert_eq!(int_smt(-5), "(- 5)");
    assert_eq!(int_smt(0), "0");
}
