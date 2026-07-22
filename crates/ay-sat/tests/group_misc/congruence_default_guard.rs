// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_sat::{Literal, Solver, Variable};

/// Regression guard for #3378.
///
/// This parity/XOR instance can become wrong-SAT when congruence preprocessing
/// is enabled unsafely. The default solver configuration must keep congruence
/// disabled, and this benchmark must remain UNSAT.
#[test]
fn test_congruence_default_keeps_urquhart3_unsat() {
    let mut solver: Solver = Solver::new(3);
    let x1 = Literal::positive(Variable::new(0));
    let x2 = Literal::positive(Variable::new(1));
    let x3 = Literal::positive(Variable::new(2));

    // x1 XOR x2 = 1
    solver.add_clause(vec![x1, x2]);
    solver.add_clause(vec![x1.negated(), x2.negated()]);
    // x2 XOR x3 = 1
    solver.add_clause(vec![x2, x3]);
    solver.add_clause(vec![x2.negated(), x3.negated()]);
    // x3 XOR x1 = 1
    solver.add_clause(vec![x3, x1]);
    solver.add_clause(vec![x3.negated(), x1.negated()]);
    // Parity blockers
    solver.add_clause(vec![x1, x2, x3]);
    solver.add_clause(vec![x1.negated(), x2.negated(), x3.negated()]);

    assert!(
        solver.solve().is_unsat(),
        "expected UNSAT with default congruence settings"
    );
}
