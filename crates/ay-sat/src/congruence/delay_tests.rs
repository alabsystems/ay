// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::test_util::lit;

fn add_and_gate(clauses: &mut ClauseArena, output_var: usize, input_vars: &[usize]) {
    let output_var = u32::try_from(output_var).expect("test output var fits in u32");
    for &input_var in input_vars {
        let input_var = u32::try_from(input_var).expect("test input var fits in u32");
        clauses.add(&[lit(output_var, false), lit(input_var, true)], false);
    }
    let mut long_clause = Vec::with_capacity(input_vars.len() + 1);
    long_clause.push(lit(output_var, true));
    long_clause.extend(input_vars.iter().map(|&input_var| {
        let input_var = u32::try_from(input_var).expect("test input var fits in u32");
        lit(input_var, false)
    }));
    clauses.add(&long_clause, false);
}

#[test]
fn test_gate_extraction_delay_retries_after_clause_change_without_num_var_growth() {
    let mut clauses = ClauseArena::new();
    add_and_gate(&mut clauses, 0, &[2, 3]);

    let mut cc = CongruenceClosure::new(4);
    let first = cc.run(&mut clauses, None, &[]);
    assert!(
        !first.found_equivalences,
        "single gate should not produce congruence equivalences"
    );
    let gates_after_first = cc.stats().gates_analyzed;
    assert!(
        gates_after_first > 0,
        "first run must actually analyze the original gate"
    );

    // Keep num_vars flat and only mutate clauses. The old permanent skip cache
    // would never re-run gate extraction here, so y0 ≡ y1 stayed invisible.
    add_and_gate(&mut clauses, 1, &[2, 3]);

    let second = cc.run(&mut clauses, None, &[]);
    assert!(
        !second.found_equivalences,
        "delay should skip one retry immediately after a fruitless gate round"
    );
    assert_eq!(
        cc.stats().gates_analyzed,
        gates_after_first,
        "delayed retry must not rescan gates immediately"
    );

    let third = cc.run(&mut clauses, None, &[]);
    assert!(
        third.found_equivalences,
        "gate extraction must retry after the delay even when num_vars is unchanged"
    );
    assert!(
        cc.stats().gates_analyzed > gates_after_first,
        "successful retry should rescan gates after the delay expires"
    );

    let y0 = lit(0, true);
    let y1 = lit(1, true);
    assert!(
        third
            .equivalence_edges
            .iter()
            .any(|&(a, b)| (a == y0 && b == y1) || (a == y1 && b == y0)),
        "retry should expose y0 ≡ y1 after the clause-only change, got {:?}",
        third.equivalence_edges
    );
}
