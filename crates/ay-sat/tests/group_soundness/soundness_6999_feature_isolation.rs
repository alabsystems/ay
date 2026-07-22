// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #6999/#7037 regression test: sweep soundness on AProVE09-13.
//!
//! History: kitten sweep's incremental probing accumulated level-0 units
//! across probes, causing false backbone/equivalence claims from over-constrained
//! sub-problems. Fix (#7037): rebuild kitten from COI clauses before each probe,
//! ensuring each backbone/equivalence test runs on a clean COI state.
//!
//! Both tests now expect correct SAT results.

use ay_sat::{parse_dimacs, SatResult, Solver};

/// Verify that pure CDCL (all inprocessing disabled, no sweep) produces
/// correct SAT on AProVE09-13.
#[test]
fn baseline_no_inprocessing_sat() {
    let path = super::common::workspace_root()
        .join("reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/sat/AProVE09-13.cnf");
    let cnf = match std::fs::read_to_string(&path) {
        Ok(c) => c,
        Err(_) => return,
    };
    let formula = parse_dimacs(&cnf).expect("parse");
    let mut solver = Solver::new(formula.num_vars);
    solver.set_vivify_enabled(false);
    solver.set_subsume_enabled(false);
    solver.set_probe_enabled(false);
    solver.set_shrink_enabled(false);
    solver.set_bve_enabled(false);
    solver.set_bce_enabled(false);
    solver.set_decompose_enabled(false);
    solver.set_factor_enabled(false);
    solver.set_transred_enabled(false);
    solver.set_htr_enabled(false);
    solver.set_gate_enabled(false);
    solver.set_congruence_enabled(false);
    solver.set_sweep_enabled(false);
    solver.set_condition_enabled(false);
    solver.set_hbr_enabled(false);
    solver.set_backbone_enabled(false);
    for clause in formula.clauses {
        solver.add_clause(clause);
    }
    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(_) => {} // correct
        SatResult::Unsat(_) => panic!("#6999: false-UNSAT with ALL inprocessing disabled"),
        _ => {} // Unknown is acceptable (solver limits)
    }
}

/// Verify that sweep-only (all other techniques disabled) produces correct
/// SAT on AProVE09-13. Previously (#6999) this produced false-UNSAT due to
/// accumulated level-0 units corrupting kitten probes. Fixed by #7037
/// rebuild-per-probe.
#[test]
fn sweep_only_produces_correct_sat() {
    let path = super::common::workspace_root()
        .join("reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/sat/AProVE09-13.cnf");
    let cnf = match std::fs::read_to_string(&path) {
        Ok(c) => c,
        Err(_) => return,
    };
    let formula = parse_dimacs(&cnf).expect("parse");
    let mut solver = Solver::new(formula.num_vars);

    solver.set_vivify_enabled(false);
    solver.set_subsume_enabled(false);
    solver.set_probe_enabled(false);
    solver.set_shrink_enabled(false);
    solver.set_bve_enabled(false);
    solver.set_bce_enabled(false);
    solver.set_decompose_enabled(false);
    solver.set_factor_enabled(false);
    solver.set_transred_enabled(false);
    solver.set_htr_enabled(false);
    solver.set_gate_enabled(false);
    solver.set_congruence_enabled(false);
    solver.set_sweep_enabled(true);
    solver.set_condition_enabled(false);
    solver.set_hbr_enabled(false);
    solver.set_backbone_enabled(false);

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(_) => {} // correct — sweep is now sound
        SatResult::Unsat(_) => {
            panic!("#7037 regression: sweep-only still produces false-UNSAT on AProVE09-13")
        }
        _ => {} // Unknown is acceptable (solver limits)
    }
}
