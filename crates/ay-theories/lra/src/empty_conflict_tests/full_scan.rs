// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Full-scan empty-conflict regression.

use super::*;

#[test]
fn test_full_scan_detects_contradiction_on_high_index_var_9061() {
    // #9061: the early contradictory-bounds scan on the full (non-targeted)
    // path iterated a fixed 64-element buffer, so a variable with index >= 64
    // was never checked. A plain contradiction there (lower > upper, both
    // bounds asserted) went undetected; with no row to pivot it, the non-basic
    // repair loop oscillated the variable between its two bounds until
    // `max_iters`, returning a spurious Unknown instead of the correct UNSAT.
    // This poisoned reified Bool-over-LIA gate problems (kind2
    // microwave03/SYNAPSE/ticket3i) and AUFLIA-array Unknowns, which routinely
    // carry hundreds of variables.
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let lo_reason = terms.mk_ge(a, zero); // asserted gate atom for the lower bound
    let up_reason = terms.mk_ge(b, zero); // distinct asserted gate atom for the upper bound

    let mut solver = LraSolver::new(&terms);
    // 65 feasible, unconstrained non-basic variables occupy indices 0..=64.
    for _ in 0..65 {
        solver.vars.push(VarInfo {
            value: InfRational::from_rational(bi(0)),
            lower: None,
            upper: None,
            status: Some(VarStatus::NonBasic),
        });
    }
    // Index 65 (>= 64): contradictory bounds lower=639 > upper=0, both with
    // live (asserted) reasons; the current value sits below the lower bound.
    solver.vars.push(VarInfo {
        value: InfRational::from_rational(bi(0)),
        lower: Some(Bound::new(
            bi(639).into(),
            vec![lo_reason],
            vec![true],
            Vec::new(),
            false,
        )),
        upper: Some(Bound::new(
            bi(0).into(),
            vec![up_reason],
            vec![true],
            Vec::new(),
            false,
        )),
        status: Some(VarStatus::NonBasic),
    });
    // No tableau rows: the only way to "repair" var 65 is to move it, which
    // oscillates between the two incompatible bounds.
    solver.asserted.insert(lo_reason, true);
    solver.asserted.insert(up_reason, true);

    // Large budget (> 100) so the full, non-targeted early scan path runs and a
    // missed contradiction would spin to max_iters.
    let result = solver.dual_simplex_with_max_iters(30_000);
    let lits = match result {
        TheoryResult::UnsatWithFarkas(c) => c.literals,
        TheoryResult::Unsat(l) => l,
        other => panic!(
            "contradiction on variable index >= 64 must be detected and returned as UNSAT, \
             not spin to a spurious Unknown; got {other:?}"
        ),
    };
    let cited: Vec<TermId> = lits.iter().map(|l| l.term).collect();
    assert!(
        cited.contains(&lo_reason) && cited.contains(&up_reason),
        "conflict must cite both contradictory bound reasons, got {cited:?}"
    );
}
