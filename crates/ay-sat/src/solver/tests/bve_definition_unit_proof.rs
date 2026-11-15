// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A unit that BVE's definition kitten derives from a one-sided core is implied
//! by resolution over the pivot's occurrences, not by unit propagation. The
//! proof must carry the core's lemmas, lifted by the unit, before the unit
//! itself (Kissat definition.c, `traverse_one_sided_core_lemma`), or the
//! DRAT and VeriPB checkers reject the unit: measured on cabp-M k33's arm C on
//! 2026-09-16, "proofgoal could not be autoproven" on `red 1 x99978 >= 1`.

use super::*;
use crate::ProofOutput;

fn pos(v: u32) -> Literal {
    Literal::positive(Variable(v))
}
fn neg(v: u32) -> Literal {
    Literal::negative(Variable(v))
}

/// Verify `proof` (DRAT text) against `clauses` with the standalone checker.
fn verify_drat(num_vars: usize, clauses: &[Vec<Literal>], proof: &[u8]) -> Result<(), String> {
    let mut cnf = format!("p cnf {num_vars} {}\n", clauses.len());
    for clause in clauses {
        for lit in clause {
            cnf.push_str(&lit.to_dimacs().to_string());
            cnf.push(' ');
        }
        cnf.push_str("0\n");
    }
    let parsed = ay_drat_check::cnf_parser::parse_cnf(cnf.as_bytes()).map_err(|e| e.to_string())?;
    let steps = ay_drat_check::drat_parser::parse_drat(proof).map_err(|e| e.to_string())?;
    let mut checker = ay_drat_check::checker::DratChecker::new(parsed.num_vars, true);
    checker
        .verify(&parsed.clauses, &steps)
        .map_err(|e| e.to_string())
}

/// x0's positive occurrences minus x0 are the four clauses over (x1, x2) that
/// no assignment satisfies: refutable by resolution, not by propagation, so
/// the definition kitten's one-sided core yields the unit x0, which is not RUP.
/// x0's negative occurrences minus their pivot are satisfiable, so the core
/// cannot come from that side. Once x0 holds, propagation reaches the empty
/// clause through x3, x4, x5 and x6.
fn one_sided_core_formula() -> Vec<Vec<Literal>> {
    vec![
        vec![pos(0), pos(1), pos(2)],
        vec![pos(0), neg(1), pos(2)],
        vec![pos(0), pos(1), neg(2)],
        vec![pos(0), neg(1), neg(2)],
        vec![neg(0), pos(3)],
        vec![neg(0), pos(4)],
        vec![neg(3), neg(4), pos(5)],
        vec![neg(5), pos(6)],
        vec![neg(5), neg(6)],
    ]
}

#[test]
fn a_definition_kitten_unit_is_certified_by_its_lifted_core_lemmas() {
    let clauses = one_sided_core_formula();
    let num_vars = 7;
    let mut solver: Solver =
        Solver::with_proof_output(num_vars, ProofOutput::drat_text(Vec::<u8>::new()));
    for clause in &clauses {
        solver.add_clause_db(clause, false);
    }
    solver.set_gate_enabled(true);
    // Keep the other variables out of elimination, so x0 is the pivot.
    for v in 1..num_vars as u32 {
        solver.freeze(Variable(v));
    }
    let derived_unsat = solver.bve();
    // The unit is enqueued during BVE and propagated by the dense pass that
    // follows it in preprocessing; here that pass reaches the empty clause.
    let unsat = derived_unsat || solver.propagate_dense_check_unsat();
    let extractions = solver.gate_stats().extraction_calls;
    assert!(extractions > 0, "the definition kitten must have run on x0");
    let writer = solver
        .take_proof_writer()
        .expect("proof writer should exist with DRAT output");
    let text = String::from_utf8(writer.into_vec().expect("flush")).expect("utf8");
    let unit_line = text
        .lines()
        .position(|line| line.split_whitespace().collect::<Vec<_>>() == ["1", "0"])
        .expect("the proof must add the unit x0");
    assert!(
        text.lines().take(unit_line).any(|line| {
            let lits: Vec<&str> = line.split_whitespace().collect();
            !line.starts_with('d') && lits.len() > 2 && lits.contains(&"1")
        }),
        "a lifted core lemma must precede the unit: proof\n{text}"
    );
    assert!(
        unsat,
        "the formula is UNSAT once x0 holds: proof
{text}"
    );
    verify_drat(num_vars, &clauses, text.as_bytes()).unwrap_or_else(|e| {
        panic!("the standalone DRAT checker must accept every step: {e}\nproof\n{text}")
    });
}
