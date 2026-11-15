// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An input clause above `OVERSIZED_CLAUSE_SPLIT_THRESHOLD` literals is split
//! into a ladder of links over fresh variables. Under a DRAT/VeriPB surface
//! the links must reach the checker as derived clauses (2026-09-17 audit: the
//! first deletion of a link was `Constraint not found in database`), and the
//! linking variables must stay off the DIMACS model line.

use super::*;
use crate::solver::clause_add::OVERSIZED_CLAUSE_SPLIT_THRESHOLD;
use crate::ProofOutput;

fn pos(v: usize) -> Literal {
    Literal::positive(Variable(v as u32))
}
fn neg(v: usize) -> Literal {
    Literal::negative(Variable(v as u32))
}

/// `(x_0 v ... v x_{n-1})` with `n` above the threshold, `¬x_i` for every
/// `i >= 1`, and `(¬x_0 v y) (¬x_0 v ¬y)`: UNSAT by propagation through the
/// big clause, which the solver holds only as its ladder.
fn oversized_unsat(n: usize) -> (usize, Vec<Vec<Literal>>) {
    let y = n;
    let mut clauses = vec![(0..n).map(pos).collect::<Vec<_>>()];
    clauses.extend((1..n).map(|i| vec![neg(i)]));
    clauses.push(vec![neg(0), pos(y)]);
    clauses.push(vec![neg(0), neg(y)]);
    (n + 1, clauses)
}

fn cnf_text(num_vars: usize, clauses: &[Vec<Literal>]) -> String {
    let mut text = format!("p cnf {num_vars} {}\n", clauses.len());
    for clause in clauses {
        for lit in clause {
            text.push_str(&lit.to_dimacs().to_string());
            text.push(' ');
        }
        text.push_str("0\n");
    }
    text
}

#[test]
fn the_split_ladder_is_derived_in_the_proof_and_the_input_clause_deleted() {
    let n = OVERSIZED_CLAUSE_SPLIT_THRESHOLD + 1;
    let (num_vars, clauses) = oversized_unsat(n);
    let mut solver: Solver =
        Solver::with_proof_output(num_vars, ProofOutput::drat_text(Vec::<u8>::new()));
    for clause in &clauses {
        assert!(solver.add_clause(clause.clone()));
    }
    assert_eq!(solver.user_num_vars(), num_vars + 1, "one linking variable");
    assert_eq!(
        solver.visible_model_vars(),
        num_vars,
        "the link stays off the model line"
    );
    let result = solver.solve().into_inner();
    assert!(matches!(result, SatResult::Unsat(_)), "got {result:?}");
    let writer = solver.take_proof_writer().expect("DRAT writer");
    let proof = writer.into_vec().expect("flush");
    let text = String::from_utf8(proof.clone()).expect("utf8");
    let first_link_derived = text
        .lines()
        .any(|l| !l.starts_with('d') && l.split_whitespace().count() > 1000);
    let input_clause_deleted = text
        .lines()
        .any(|l| l.starts_with('d') && l.split_whitespace().count() > 60_000);
    assert!(
        first_link_derived && input_clause_deleted,
        "the first link must be derived and the input clause deleted:\n{}",
        &text[..text.len().min(300)]
    );
    let cnf = cnf_text(num_vars, &clauses);
    let parsed = ay_drat_check::cnf_parser::parse_cnf(cnf.as_bytes()).expect("cnf");
    let steps = ay_drat_check::drat_parser::parse_drat(&proof).expect("drat");
    let mut checker = ay_drat_check::checker::DratChecker::new(parsed.num_vars, true);
    checker
        .verify(&parsed.clauses, &steps)
        .unwrap_or_else(|e| panic!("the DRAT checker rejects the proof: {e}"));
}

#[test]
fn a_satisfiable_oversized_clause_keeps_its_model_within_the_header() {
    let n = OVERSIZED_CLAUSE_SPLIT_THRESHOLD + 1;
    let y = n;
    let clauses = vec![(0..n).map(pos).collect::<Vec<_>>(), vec![neg(0), pos(y)]];
    let num_vars = n + 1;
    let mut solver: Solver = Solver::new(num_vars);
    for clause in &clauses {
        assert!(solver.add_clause(clause.clone()));
    }
    let result = solver.solve().into_inner();
    let SatResult::Sat(model) = result else {
        panic!("got {result:?}");
    };
    let visible = solver.visible_model_vars();
    assert_eq!(visible, num_vars);
    let shown = &model[..visible.min(model.len())];
    for clause in &clauses {
        assert!(
            clause
                .iter()
                .any(|lit| shown[lit.variable().index()] == lit.is_positive()),
            "the visible model falsifies a clause"
        );
    }
}
