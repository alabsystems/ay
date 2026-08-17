// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::Sort;

use super::*;

#[test]
fn minimizer_envelope_restores_completed_sidecar_and_array_markers() {
    let mut executor = Executor::new();
    let proposition = executor
        .ctx
        .terms
        .mk_fresh_var("core_envelope_sidecar_p", Sort::Bool);
    let not_proposition = executor.ctx.terms.mk_not_raw(proposition);
    executor.ctx.assertions = vec![proposition, not_proposition];
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[]);
    let proposed = executor
        .check_sat()
        .expect("contradictory units must solve");
    assert!(proposed.is_unsat());
    assert!(executor.last_checked_sat_refutation.is_some());

    executor.nested_array_row_reduction_unsat = true;
    executor.ho_seq_unfold_array_free_unsat = true;
    let result = executor
        .minimize_assumption_core(&[], Ok(proposed), None)
        .expect("empty-core envelope must not fail");

    assert!(result.is_unsat());
    assert!(executor.last_checked_sat_refutation.is_some());
    assert!(executor.nested_array_row_reduction_unsat);
    assert!(executor.ho_seq_unfold_array_free_unsat);
    assert!(executor.pending_nested_array_bool_bv_unsat.is_none());
}
