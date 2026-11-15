// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

//! Primitive full-adder checks over emitted CNF, without a SAT solver.

use super::*;

#[path = "../tests/division_carry/cnf.rs"]
mod cnf;
mod integration;
mod legacy;
mod reset;

use cnf::{bit_value, word_value, Circuit};

fn setup_store() -> TermStore {
    TermStore::new()
}

fn fresh_word(solver: &mut BvSolver<'_>, width: usize) -> BvBits {
    solver.batch_fresh_vars(width).to_vec()
}

fn fix_word(bits: &[CnfLit], value: u64) -> Vec<CnfLit> {
    assert!(bits.len() <= 64);
    bits.iter()
        .enumerate()
        .map(|(index, &lit)| {
            if value & (1_u64 << index) != 0 {
                lit
            } else {
                -lit
            }
        })
        .collect()
}

fn counts(solver: &BvSolver<'_>) -> (u32, usize, usize) {
    (
        solver.num_vars(),
        solver.clauses().len(),
        solver
            .clauses()
            .iter()
            .map(|clause| clause.literals().len())
            .sum(),
    )
}

fn count_delta(after: (u32, usize, usize), before: (u32, usize, usize)) -> (u32, usize, usize) {
    (after.0 - before.0, after.1 - before.1, after.2 - before.2)
}

fn signed_inputs(solver: &mut BvSolver<'_>, signs: u64) -> (BvBits, [CnfLit; 3]) {
    let inputs = fresh_word(solver, 3);
    let selected = std::array::from_fn(|index| {
        if signs & (1 << index) == 0 {
            inputs[index]
        } else {
            -inputs[index]
        }
    });
    (inputs, selected)
}

fn input_alphabet(solver: &mut BvSolver<'_>) -> (BvBits, [CnfLit; 8]) {
    let inputs = fresh_word(solver, 3);
    let t = solver.fresh_true();
    let f = solver.fresh_false();
    let alphabet = [
        inputs[0], -inputs[0], inputs[1], -inputs[1], inputs[2], -inputs[2], t, f,
    ];
    (inputs, alphabet)
}

fn assert_full_adder_truth(model: &[Option<bool>], args: [CnfLit; 3], output: (CnfLit, CnfLit)) {
    let total: u8 = args
        .into_iter()
        .map(|lit| u8::from(bit_value(model, lit)))
        .sum();
    assert_eq!(bit_value(model, output.0), total & 1 != 0);
    assert_eq!(bit_value(model, output.1), total >= 2);
}

#[test]
fn every_signed_aliased_and_constant_triple_forces_exact_full_adder_truth() {
    let store = setup_store();
    for ai in 0..8 {
        for bi in 0..8 {
            for ci in 0..8 {
                let mut solver = BvSolver::new(&store);
                let (inputs, alphabet) = input_alphabet(&mut solver);
                let args = [alphabet[ai], alphabet[bi], alphabet[ci]];
                let output = solver.full_adder(args[0], args[1], args[2]);
                let circuit = Circuit::new(&solver);
                for assignment in 0..8 {
                    let model = circuit.propagate(&fix_word(&inputs, assignment));
                    assert_full_adder_truth(&model, args, output);
                }
            }
        }
    }
}

#[test]
fn constant_input_calls_preserve_frozen_outputs_and_exact_clause_order() {
    let store = setup_store();
    for ai in 0..8 {
        for bi in 0..8 {
            for ci in 0..8 {
                if ai < 6 && bi < 6 && ci < 6 {
                    continue;
                }
                let mut solver = BvSolver::new(&store);
                let (inputs, alphabet) = input_alphabet(&mut solver);
                let mut old = BvSolver::new(&store);
                let (old_inputs, old_alphabet) = input_alphabet(&mut old);
                assert_eq!(inputs, old_inputs);
                assert_eq!(alphabet, old_alphabet);
                let args = [alphabet[ai], alphabet[bi], alphabet[ci]];
                let output = solver.full_adder(args[0], args[1], args[2]);
                let previous = legacy::full_adder(&mut old, args[0], args[1], args[2]);
                assert_eq!(output, previous, "literal indices {ai}/{bi}/{ci}");
                assert_eq!(counts(&solver), counts(&old));
                assert_eq!(solver.clauses(), old.clauses());
                let circuit = Circuit::new(&solver);
                for assignment in 0..8 {
                    let model = circuit.propagate(&fix_word(&inputs, assignment));
                    assert_full_adder_truth(&model, args, output);
                }
            }
        }
    }
}

#[test]
fn cold_distinct_inputs_use_three_gates_twelve_clauses_and_thirty_six_literals() {
    let store = setup_store();
    for signs in 0..8 {
        let mut solver = BvSolver::new(&store);
        let (inputs, args) = signed_inputs(&mut solver, signs);
        let before = counts(&solver);
        let output = solver.full_adder(args[0], args[1], args[2]);
        assert_eq!(count_delta(counts(&solver), before), (3, 12, 36));
        let mut old = BvSolver::new(&store);
        let (old_inputs, old_args) = signed_inputs(&mut old, signs);
        assert_eq!(inputs, old_inputs);
        assert_eq!(args, old_args);
        let old_before = counts(&old);
        let previous = legacy::full_adder(&mut old, args[0], args[1], args[2]);
        assert_eq!(count_delta(counts(&old), old_before), (5, 17, 45));
        let circuit = Circuit::new(&solver);
        let old_circuit = Circuit::new(&old);
        for assignment in 0..8 {
            let fixes = fix_word(&inputs, assignment);
            assert_full_adder_truth(&circuit.propagate(&fixes), args, output);
            assert_full_adder_truth(&old_circuit.propagate(&fixes), args, previous);
        }
    }
}

#[test]
fn repeated_and_reversed_distinct_addends_reuse_the_same_signed_gate_keys() {
    let store = setup_store();
    for signs in 0..8 {
        let mut solver = BvSolver::new(&store);
        let (_, args) = signed_inputs(&mut solver, signs);
        // Start in reverse order as well: warm-cache identity cannot depend
        // on whether the first caller happened to present canonical addends.
        let output = solver.full_adder(args[1], args[0], args[2]);
        let before = counts(&solver);
        let clauses = solver.clauses().to_vec();
        for _ in 0..3 {
            assert_eq!(solver.full_adder(args[0], args[1], args[2]), output);
            assert_eq!(solver.full_adder(args[1], args[0], args[2]), output);
            assert_eq!(counts(&solver), before);
            assert_eq!(solver.clauses(), clauses.as_slice());
        }
    }
}

fn canonical_clauses(solver: &BvSolver<'_>) -> Vec<Vec<CnfLit>> {
    let mut clauses = solver
        .clauses()
        .iter()
        .map(|clause| {
            let mut lits = clause.literals().to_vec();
            lits.sort_unstable();
            lits
        })
        .collect::<Vec<_>>();
    clauses.sort_unstable();
    clauses
}

#[test]
fn captured_xor_mux_provenance_reconstructs_the_full_cnf_and_exact_gate_truth() {
    let store = setup_store();
    for signs in 0..8 {
        let mut solver = BvSolver::new(&store);
        solver.enable_gate_provenance();
        let (inputs, args) = signed_inputs(&mut solver, signs);
        let output = solver.full_adder(args[0], args[1], args[2]);
        assert!(solver.and_children().is_empty());
        assert_eq!(solver.xor_children().len(), 2);
        assert_eq!(solver.mux_children().len(), 1);
        let mut templates = solver
            .xor_children()
            .iter()
            .map(|(&out, &(a, b))| (out, BvGateTemplate::xor(a, b, out)))
            .chain(
                solver
                    .mux_children()
                    .iter()
                    .map(|(&out, &(sel, then_lit, else_lit))| {
                        (out, BvGateTemplate::mux(sel, then_lit, else_lit, out))
                    }),
            )
            .collect::<Vec<_>>();
        templates.sort_unstable_by_key(|(out, _)| *out);
        let mut rebuilt = BvSolver::new(&store);
        let _ = rebuilt.batch_fresh_vars(solver.num_vars() as usize);
        for (_, template) in templates {
            for clause in template.to_clauses() {
                rebuilt.add_clause(clause);
            }
        }
        assert_eq!(counts(&rebuilt), counts(&solver));
        // XOR child provenance stores its commutative canonical key, while
        // emission may use the reverse operand order. Compare full clause
        // multisets rather than pretending that literal ordering is identical.
        assert_eq!(canonical_clauses(&rebuilt), canonical_clauses(&solver));
        let original_circuit = Circuit::new(&solver);
        let rebuilt_circuit = Circuit::new(&rebuilt);
        for assignment in 0..8 {
            let fixes = fix_word(&inputs, assignment);
            let model = original_circuit.propagate(&fixes);
            assert_full_adder_truth(&model, args, output);
            assert_full_adder_truth(&rebuilt_circuit.propagate(&fixes), args, output);
            for (&out, &(a, b)) in solver.xor_children() {
                assert_eq!(
                    bit_value(&model, out),
                    bit_value(&model, a) ^ bit_value(&model, b)
                );
            }
            for (&out, &(sel, then_lit, else_lit)) in solver.mux_children() {
                let chosen = if bit_value(&model, sel) {
                    then_lit
                } else {
                    else_lit
                };
                assert_eq!(bit_value(&model, out), bit_value(&model, chosen));
            }
        }
    }
}
