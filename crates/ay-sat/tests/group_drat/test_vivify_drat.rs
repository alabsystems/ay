// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::common::read_barrel6;
use ay_sat::{parse_dimacs, ProofOutput, Solver};

fn run_drat_test(label: &str, enable_vivify: bool) {
    let Some(cnf) = read_barrel6() else { return };
    let formula = parse_dimacs(&cnf).unwrap();
    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver: Solver = Solver::with_proof_output(formula.num_vars, proof_writer);

    super::common::disable_all_inprocessing(&mut solver);
    if enable_vivify {
        solver.set_vivify_enabled(true);
    }

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    assert!(
        result.is_unsat(),
        "[{label}] Expected UNSAT on known-UNSAT benchmark cmu-bmc-barrel6, got {:?}",
        if result.is_sat() { "SAT" } else { "Unknown" },
    );

    let writer = solver.take_proof_writer().unwrap();
    let proof_bytes = writer.into_vec().expect("proof flush");
    super::common::verify_drat_proof(&cnf, &proof_bytes, label);
}

#[test]
fn drat_baseline_no_inprocessing() {
    run_drat_test("baseline", false);
}

#[test]
fn drat_vivify_only() {
    run_drat_test("vivify", true);
}
