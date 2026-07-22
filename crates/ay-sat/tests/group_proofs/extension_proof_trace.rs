// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_sat::{
    ClauseTraceEntry, ExtCheckResult, ExtPropagateResult, Extension, Literal, Solver,
    SolverContext, Variable,
};

struct NoopExtension;

impl Extension for NoopExtension {
    fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
        ExtPropagateResult::none()
    }

    fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
        ExtCheckResult::Sat
    }

    fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
        false
    }
}

#[test]
fn test_solve_with_extension_level0_bcp_conflict_records_clause_trace_hints() {
    let mut solver = Solver::new(2);
    solver.enable_clause_trace();

    let a = Literal::positive(Variable::new(0));
    let c = Literal::positive(Variable::new(1));

    assert!(solver.add_clause(vec![a]));
    assert!(solver.add_clause(vec![a.negated(), c]));
    assert!(solver.add_clause(vec![a.negated(), c.negated()]));

    let mut ext = NoopExtension;
    let result = solver.solve_with_extension(&mut ext).into_inner();
    assert!(
        result.is_unsat(),
        "level-0 BCP contradiction in solve_with_extension must return UNSAT"
    );

    let trace = solver.take_clause_trace().expect("clause trace enabled");
    assert!(
        trace.has_empty_clause(),
        "trace must record derived empty clause"
    );
    assert_eq!(trace.len(), 4, "3 original clauses + derived empty clause");

    let empty_entry: &ClauseTraceEntry = trace.entries().last().expect("empty clause entry");
    assert!(
        empty_entry.clause.is_empty(),
        "final clause-trace entry must be the empty clause"
    );
    assert!(
        !empty_entry.is_original,
        "derived empty clause must be marked learned"
    );
    assert_eq!(
        empty_entry.resolution_hints,
        vec![3, 2, 1],
        "extension init loop must record conflict + reason clause IDs in trail-reverse order"
    );
}
