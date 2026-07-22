// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::*;

#[test]
fn test_sbva_integration_basic() {
    // Create a solver with clauses that have a compressible structure.
    // 3 clauses sharing {a, b, c} with different tails:
    // {a, b, c, d}
    // {a, b, c, e}
    // {a, b, c, f}
    let mut solver = Solver::new(10);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));
    let d = Literal::positive(Variable(3));
    let e = Literal::positive(Variable(4));
    let f = Literal::positive(Variable(5));

    solver.add_clause(vec![a, b, c, d]);
    solver.add_clause(vec![a, b, c, e]);
    solver.add_clause(vec![a, b, c, f]);

    let _clauses_before = solver.arena.active_clause_count();
    let vars_before = solver.num_vars;

    // Run SBVA directly.
    solver.sbva();

    // SBVA should have introduced extension vars and rewritten clauses.
    // The exact behavior depends on scheduling guards, so just verify no crash
    // and basic structural invariants hold.
    assert!(
        solver.num_vars >= vars_before,
        "num_vars should not decrease after SBVA"
    );
    // Clause count may change (original deleted, new added).
    let clauses_after = solver.arena.active_clause_count();
    assert!(clauses_after > 0, "should have at least some clauses");
}

#[test]
fn test_sbva_records_er_extension_definition_log() {
    let mut solver = Solver::new(10);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));
    let d = Literal::positive(Variable(3));
    let e = Literal::positive(Variable(4));
    let f = Literal::positive(Variable(5));

    solver.add_clause(vec![a, b, c, d]);
    solver.add_clause(vec![a, b, c, e]);
    solver.add_clause(vec![a, b, c, f]);

    solver.sbva();

    assert_eq!(
        solver.er_extension_definition_count(),
        1,
        "one SBVA extension variable must have one ER definition artifact"
    );
    let def = &solver.er_extension_proof_log().definitions()[0];
    assert_eq!(def.producer(), crate::er_proof::ErProducer::Sbva);
    assert_eq!(def.definition_clauses().len(), 1);
    assert_eq!(def.derived_clauses().len(), 3);
    assert_eq!(def.proof_only_clauses().len(), 1);
    assert_eq!(def.source_clause_ids(), &[1, 2, 3]);

    let mut buf = Vec::new();
    solver
        .write_er_extension_log_proof_replay(&mut buf)
        .expect("write ER log");
    let source = String::from_utf8(buf).expect("utf8");
    assert!(source.contains("Producer.sbva"));
    assert!(source.contains("theorem er_extension_log_structural_ok"));
    assert!(
        !source.contains("heuristicScore") && !source.contains("candidate"),
        "ER artifact must not include heuristic selection data"
    );
}

#[test]
fn test_sbva_incremental_guard() {
    // SBVA should be skipped in incremental mode.
    let mut solver = Solver::new(10);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));
    let d = Literal::positive(Variable(3));
    let e = Literal::positive(Variable(4));
    let f = Literal::positive(Variable(5));

    solver.add_clause(vec![a, b, c, d]);
    solver.add_clause(vec![a, b, c, e]);
    solver.add_clause(vec![a, b, c, f]);

    solver.cold.has_been_incremental = true;
    let vars_before = solver.num_vars;

    solver.sbva();

    assert_eq!(
        solver.num_vars, vars_before,
        "SBVA should not introduce new vars in incremental mode"
    );
}

#[test]
fn test_sbva_build_occ() {
    let mut solver = Solver::new(8);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));
    let d = Literal::positive(Variable(3));
    let e = Literal::positive(Variable(4));

    // Binary clause -- should NOT be in SBVA occ.
    solver.add_clause(vec![a, b]);
    // 3-literal clause -- should be in SBVA occ.
    solver.add_clause(vec![a, b, c]);
    // 4-literal clause -- should be in SBVA occ.
    solver.add_clause(vec![a, c, d, e]);

    let occ = solver.build_sbva_occ();

    // Binary clause not counted.
    // 'a' appears in 2 clauses (the 3-lit and 4-lit ones).
    assert_eq!(
        occ.count(a),
        2,
        "'a' should appear in 2 SBVA-eligible clauses"
    );
    // 'b' appears in 1 clause (the 3-lit one; binary excluded).
    assert_eq!(
        occ.count(b),
        1,
        "'b' should appear in 1 SBVA-eligible clause"
    );
}
