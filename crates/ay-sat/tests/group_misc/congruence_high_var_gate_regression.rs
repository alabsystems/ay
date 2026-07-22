// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_sat::{Literal, SatResult, Solver, Variable};

#[test]
fn test_congruence_reaches_high_numbered_duplicate_gate_outputs() {
    let mut solver = Solver::new(10_004);
    solver.disable_all_inprocessing();
    solver.set_gate_enabled(true);
    solver.set_congruence_enabled(true);
    solver.set_decompose_enabled(true);

    let a = Literal::positive(Variable::new(0));
    let b = Literal::positive(Variable::new(1));
    let y0 = Literal::positive(Variable::new(9_500));
    let y1 = Literal::positive(Variable::new(9_501));

    // y0 = AND(a, b)
    assert!(solver.add_clause(vec![y0.negated(), a]));
    assert!(solver.add_clause(vec![y0.negated(), b]));
    assert!(solver.add_clause(vec![y0, a.negated(), b.negated()]));

    // y1 = AND(a, b)
    assert!(solver.add_clause(vec![y1.negated(), a]));
    assert!(solver.add_clause(vec![y1.negated(), b]));
    assert!(solver.add_clause(vec![y1, a.negated(), b.negated()]));

    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Sat(_)),
        "duplicate-gate formula must stay SAT, got {result:?}"
    );

    let congruence = solver.congruence_stats();
    let decompose = solver.decompose_stats();
    assert!(
        congruence.equivalences_found > 0 || decompose.substituted > 0,
        "high-numbered duplicate gates should trigger congruence or decompose \
         (equivalences_found={}, substituted={})",
        congruence.equivalences_found,
        decompose.substituted
    );
}
