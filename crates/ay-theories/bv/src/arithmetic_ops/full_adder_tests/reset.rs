// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::*;

fn rebuild_provenance<'a>(solver: &BvSolver<'_>, store: &'a TermStore) -> BvSolver<'a> {
    let mut templates = solver
        .and_children()
        .iter()
        .map(|(&out, &(a, b))| (out, BvGateTemplate::and(a, b, out)))
        .chain(
            solver
                .xor_children()
                .iter()
                .map(|(&out, &(a, b))| (out, BvGateTemplate::xor(a, b, out))),
        )
        .chain(
            solver
                .mux_children()
                .iter()
                .map(|(&out, &(sel, a, b))| (out, BvGateTemplate::mux(sel, a, b, out))),
        )
        .collect::<Vec<_>>();
    templates.sort_unstable_by_key(|(out, _)| *out);
    let mut rebuilt = BvSolver::new(store);
    rebuilt.batch_fresh_vars(solver.num_vars() as usize);
    for (_, template) in templates {
        for clause in template.to_clauses() {
            rebuilt.add_clause(clause);
        }
    }
    rebuilt
}

#[test]
fn reset_retires_reverse_provenance_before_reusing_output_ids_for_other_gate_kinds() {
    let store = setup_store();
    let mut solver = BvSolver::new(&store);
    solver.enable_gate_provenance();
    let inputs = fresh_word(&mut solver, 3);
    solver.full_adder(inputs[0], inputs[1], inputs[2]);
    assert_eq!(solver.xor_children().len(), 2);
    assert_eq!(solver.mux_children().len(), 1);
    assert!(solver.xor_children().contains_key(&4));
    assert!(solver.mux_children().contains_key(&6));

    solver.reset();
    assert_eq!(solver.num_vars(), 0);
    assert_eq!(solver.clauses(), &[] as &[CnfClause]);
    assert!(solver.and_children().is_empty());
    assert!(solver.xor_children().is_empty());
    assert!(solver.mux_children().is_empty());

    let new_inputs = fresh_word(&mut solver, 3);
    assert_eq!(new_inputs, inputs);
    let and = solver.mk_and(inputs[0], inputs[1]);
    assert_eq!(and, 4); // Previously an XOR output, now solely an AND output.
    assert!(solver.xor_children().is_empty());
    assert!(solver.mux_children().is_empty());
    let xor = solver.mk_xor(inputs[0], inputs[2]);
    let mux = solver.mk_mux(and, xor, inputs[1]);
    assert_eq!((xor, mux), (5, 6));
    // Reset preserves the opt-in capture policy, but not any previous record.
    assert_eq!(solver.and_children().len(), 1);
    assert_eq!(solver.xor_children().len(), 1);
    assert_eq!(solver.mux_children().len(), 1);
    let rebuilt = rebuild_provenance(&solver, &store);
    assert_eq!(counts(&rebuilt), counts(&solver));
    assert_eq!(canonical_clauses(&rebuilt), canonical_clauses(&solver));
    let circuit = Circuit::from_clauses(solver.num_vars(), solver.clauses());
    let rebuilt_circuit = Circuit::from_clauses(rebuilt.num_vars(), rebuilt.clauses());
    for assignment in 0..8 {
        let fixes = fix_word(&inputs, assignment);
        let model = circuit.propagate(&fixes);
        let replayed = rebuilt_circuit.propagate(&fixes);
        let a = assignment & 1 != 0;
        let b = assignment & 2 != 0;
        let c = assignment & 4 != 0;
        for (output, expected) in [
            (and, a && b),
            (xor, a ^ c),
            (mux, if b { a && b } else { a ^ c }),
        ] {
            assert_eq!(bit_value(&model, output), expected);
            assert_eq!(bit_value(&replayed, output), expected);
        }
    }
}
