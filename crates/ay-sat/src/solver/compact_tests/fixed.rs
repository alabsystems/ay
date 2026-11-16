// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! `--sat-compact-fixed`: compaction drops root-fixed variables, models keep
//! their values, and a refutation after the drop has a valid DRAT proof.

use super::*;
use crate::{Literal, ProofOutput, SatResult, Variable};

/// Variables `0..CHAIN` are fixed true at the root.
const CHAIN: usize = 120;

fn var(index: usize) -> Literal {
    Literal::positive(Variable(index as u32))
}

/// Free variable `j`, numbered after the chain.
fn free(j: usize) -> Literal {
    var(CHAIN + j)
}

/// The unit `x0` and the implications `x_i -> x_{i+1}`, which fix the whole
/// chain at the root, followed by `free_clauses`.
fn chain_clauses(free_clauses: &[Vec<Literal>]) -> Vec<Vec<Literal>> {
    let mut clauses = vec![vec![var(0)]];
    for i in 0..CHAIN - 1 {
        clauses.push(vec![var(i).negated(), var(i + 1)]);
    }
    clauses.extend_from_slice(free_clauses);
    clauses
}

fn switches(on: bool) -> ay_core::SatAbSwitches {
    ay_core::SatAbSwitches {
        compact_fixed: Some(on),
        ..Default::default()
    }
}

/// A solver over `chain_clauses(free_clauses)` after `init_solve`, and every
/// original clause in external numbering.
fn fixed_chain_solver(
    on: bool,
    num_free: usize,
    free_clauses: &[Vec<Literal>],
    proof: Option<ProofOutput>,
) -> (Solver, Vec<Vec<Literal>>) {
    let _switches = ay_core::sat_ab_test_override::set(switches(on));
    let num_vars = CHAIN + num_free;
    let mut solver = match proof {
        Some(proof) => Solver::with_proof_output(num_vars, proof),
        None => Solver::new(num_vars),
    };
    assert_eq!(solver.cold.compact_fixed, on);
    // The DIMACS route's one-shot solve, which the switch requires.
    solver.set_symmetry_oneshot(true);
    let clauses = chain_clauses(free_clauses);
    for clause in &clauses {
        solver.add_clause(clause.clone());
    }
    assert!(solver.init_solve().is_none(), "the fixture needs search");
    assert_eq!(solver.trail.len(), CHAIN, "the chain is fixed at the root");
    (solver, clauses)
}

/// Satisfiable over ten free variables. Some clauses carry a root-false
/// chain literal (the collection strips it) and some a root-true one (the
/// collection deletes the clause).
fn sat_free_clauses() -> Vec<Vec<Literal>> {
    vec![
        vec![free(0), free(1), var(5).negated()],
        vec![free(0).negated(), free(2), var(7)],
        vec![free(1).negated(), free(3), var(9).negated()],
        vec![free(3).negated(), free(4).negated()],
        vec![free(4), free(5), var(11).negated()],
        vec![free(5).negated(), free(6), free(7)],
        vec![free(6).negated(), free(7).negated(), var(13).negated()],
        vec![free(8), free(9)],
        vec![free(8).negated(), free(9).negated()],
        vec![free(2), free(9).negated(), var(0)],
    ]
}

/// All eight sign patterns over three free variables, each widened by a
/// different root-false chain literal: unsatisfiable, but only by search.
fn unsat_free_clauses() -> Vec<Vec<Literal>> {
    (0..8usize)
        .map(|signs| {
            let mut clause: Vec<Literal> = (0..3)
                .map(|j| {
                    if ((signs >> j) & 1) == 1 {
                        free(j).negated()
                    } else {
                        free(j)
                    }
                })
                .collect();
            clause.push(var(1 + signs).negated());
            clause
        })
        .collect()
}

/// Thirty binaries and 1,250 ternaries over 300 free variables, the Kissat
/// parity test's mix near the threshold, with every other clause widened by
/// a root-false chain literal.
fn random_free_clauses(seed: u64) -> Vec<Vec<Literal>> {
    let mut state = seed.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    std::iter::repeat_n(2, 30)
        .chain(std::iter::repeat_n(3, 1_250))
        .enumerate()
        .map(|(c, width)| {
            let mut clause: Vec<Literal> = (0..width)
                .map(|_| {
                    let lit = free((next() % 300) as usize);
                    if next().is_multiple_of(2) {
                        lit
                    } else {
                        lit.negated()
                    }
                })
                .collect();
            if c.is_multiple_of(2) {
                clause.push(var(1 + c % (CHAIN - 1)).negated());
            }
            clause
        })
        .collect()
}

/// Solve the chain and `free_clauses` from scratch with BVE and subsumption
/// on: `Some(true)` with a checked model, `Some(false)` for UNSAT.
fn solve_with_chain(on: bool, free_clauses: &[Vec<Literal>]) -> Option<bool> {
    let _switches = ay_core::sat_ab_test_override::set(switches(on));
    let mut solver = Solver::new(CHAIN + 300);
    solver.set_symmetry_oneshot(true);
    solver.set_bve_enabled(true);
    solver.set_subsume_enabled(true);
    let clauses = chain_clauses(free_clauses);
    for clause in &clauses {
        solver.add_clause(clause.clone());
    }
    match solver.solve().into_inner() {
        SatResult::Sat(model) => {
            assert_model(&model, &clauses);
            Some(true)
        }
        SatResult::Unsat(_) => Some(false),
        SatResult::Unknown => None,
    }
}

fn assert_model(model: &[bool], clauses: &[Vec<Literal>]) {
    for clause in clauses {
        assert!(
            clause
                .iter()
                .any(|lit| model[lit.variable().index()] == lit.is_positive()),
            "model falsifies {clause:?}"
        );
    }
    assert!(
        model[..CHAIN].iter().all(|&value| value),
        "every fixed variable keeps its root value"
    );
}

#[test]
fn compact_fixed_off_keeps_root_fixed_variables() {
    let (mut solver, _) = fixed_chain_solver(false, 10, &sat_free_clauses(), None);
    assert!(
        !solver.compacting(),
        "by default only eliminated and substituted variables are inactive"
    );
    solver.compact();
    assert_eq!(solver.num_vars, CHAIN + 10);
    assert_eq!(solver.trail.len(), CHAIN);
    assert_eq!(solver.cold.compact_count, 0);
}

/// Extension and theory solves turn every pass that removes variables off,
/// and the CP and XOR extensions keep internal variable indices across the
/// search, so the switch must not start compacting them.
#[test]
fn compact_fixed_leaves_a_solver_without_variable_removal_alone() {
    let (mut solver, _) = fixed_chain_solver(true, 10, &sat_free_clauses(), None);
    solver.disable_extension_inprocessing();
    assert!(!solver.compact_fixed_active());
    assert!(
        !solver.compacting(),
        "the default never compacts a solver that removes no variables"
    );
    solver.compact();
    assert_eq!(solver.num_vars, CHAIN + 10);
    assert_eq!(solver.trail.len(), CHAIN);
    assert_eq!(solver.cold.compact_count, 0);
}

#[test]
fn compact_fixed_drops_root_fixed_variables_and_models_keep_their_values() {
    let (mut solver, clauses) = fixed_chain_solver(true, 10, &sat_free_clauses(), None);
    assert!(solver.compacting(), "fixed variables count as inactive");
    assert!(!solver.compact_with_fixed());

    assert_eq!(solver.num_vars, 10, "every fixed variable is dropped");
    assert_eq!(solver.cold.compact_count, 1);
    assert_eq!(solver.trail.len(), 0);
    assert_eq!(solver.qhead, 0);
    for i in 0..CHAIN {
        assert_eq!(solver.cold.e2i[i], UNMAPPED, "x{i} is compacted away");
        assert!(
            solver.cold.eliminated_ext_vals[i],
            "x{i} keeps its root value"
        );
    }
    for j in 0..10 {
        assert_eq!(solver.cold.e2i[CHAIN + j], j as u32);
        assert_eq!(solver.cold.i2e[j], (CHAIN + j) as u32);
    }
    assert!(
        solver
            .arena
            .active_indices()
            .all(|idx| solver.arena.len_of(idx) >= 2),
        "the unit clause x0 left the arena with its variable"
    );

    let SatResult::Sat(model) = solver.cdcl_loop_pure(|| false) else {
        panic!("the formula is satisfiable");
    };
    assert_model(&model, &clauses);
}

#[test]
fn compact_fixed_keeps_a_fixed_variable_a_clause_still_mentions() {
    let (mut solver, clauses) = fixed_chain_solver(true, 10, &sat_free_clauses(), None);
    // A garbage-kept husk still mentions x50. The level-0 collection skips
    // husks and compaction renumbers them, so x50 has to stay mapped.
    let husk = solver.add_clause_db(&[var(50), free(0), free(1)], true);
    solver.arena.mark_garbage_keep_data(husk);
    assert!(!solver.compact_with_fixed());

    assert_eq!(solver.num_vars, 11, "only x50 of the chain stays");
    let kept = Literal::positive(Variable(0));
    assert_eq!(solver.cold.e2i[50], 0);
    assert_eq!(solver.cold.i2e[0], 50);
    assert_eq!(solver.cold.e2i[49], UNMAPPED);
    assert_eq!(solver.trail, vec![kept], "x50 stays on the root trail");
    assert_eq!(solver.var_data[0].trail_pos, 0);
    assert_eq!(solver.var_data[0].level, 0);
    assert!(
        solver.var_lifecycle.is_fixed(0),
        "a kept root assignment stays Fixed"
    );
    assert!(solver.arena.literals(husk).contains(&kept));

    let SatResult::Sat(model) = solver.cdcl_loop_pure(|| false) else {
        panic!("the formula is satisfiable");
    };
    assert_model(&model, &clauses);
}

/// End to end through `solve`, where compaction runs at the end of an
/// inprocessing round's elimination passes: the verdicts agree with the
/// default and every model satisfies the formula.
#[test]
fn compact_fixed_agrees_with_the_default_on_random_formulas() {
    for seed in 0..6u64 {
        let free_clauses = random_free_clauses(seed);
        let off = solve_with_chain(false, &free_clauses);
        let on = solve_with_chain(true, &free_clauses);
        assert_eq!(on, off, "seed {seed}");
        assert!(off.is_some(), "seed {seed} is answered");
    }
}

#[test]
fn compact_fixed_refutation_has_a_valid_drat_proof() {
    let proof = ProofOutput::drat_text(Vec::<u8>::new());
    let (mut solver, clauses) = fixed_chain_solver(true, 3, &unsat_free_clauses(), Some(proof));
    assert!(solver.compacting(), "DRAT proofs allow compaction");
    assert!(!solver.compact_with_fixed());
    assert_eq!(solver.num_vars, 3, "every fixed variable is dropped");

    let result = solver.cdcl_loop_pure(|| false);
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "the formula is unsatisfiable"
    );
    let writer = solver.take_proof_writer().expect("DRAT writer");
    let text = String::from_utf8(writer.into_vec().expect("proof flush")).expect("UTF-8 proof");
    assert_drat_refutation(&clauses, CHAIN + 3, &text);
}

/// Check a DRAT text proof against the original clauses: no unit clause of
/// a fixed chain variable is deleted, every lemma is RUP, and the proof
/// derives the empty clause. Deletions are not replayed, so each lemma is
/// checked against every earlier clause. That is weaker than a full DRAT
/// check, but a literal externalized to the wrong variable after compaction
/// still fails it.
fn assert_drat_refutation(originals: &[Vec<Literal>], num_vars: usize, proof: &str) {
    let mut clauses: Vec<Vec<i32>> = originals
        .iter()
        .map(|clause| clause.iter().map(|lit| lit.to_dimacs()).collect())
        .collect();
    let mut refuted = false;
    for line in proof.lines().filter(|line| !line.trim().is_empty()) {
        let mut tokens = line.split_whitespace().peekable();
        let delete = tokens.peek() == Some(&"d");
        if delete {
            tokens.next();
        }
        let lits: Vec<i32> = tokens
            .map(|token| token.parse::<i32>().expect("DRAT literal"))
            .take_while(|&lit| lit != 0)
            .collect();
        assert!(
            lits.iter()
                .all(|lit| lit.unsigned_abs() as usize <= num_vars),
            "proof line {line:?} names a variable outside the formula"
        );
        if delete {
            let chain_unit = lits.len() == 1 && lits[0].unsigned_abs() as usize <= CHAIN;
            assert!(!chain_unit, "a fixed variable's unit was deleted: {line:?}");
            continue;
        }
        let negated: Vec<i32> = lits.iter().map(|&lit| -lit).collect();
        assert!(
            propagates_to_conflict(&clauses, num_vars, &negated),
            "lemma {line:?} is not RUP"
        );
        refuted |= lits.is_empty();
        clauses.push(lits);
    }
    assert!(refuted, "the proof derives the empty clause");
}

/// Unit propagation over `clauses` with every literal of `assumed` true
/// (DIMACS literals): whether it reaches a conflict.
fn propagates_to_conflict(clauses: &[Vec<i32>], num_vars: usize, assumed: &[i32]) -> bool {
    let mut value = vec![0i8; num_vars + 1];
    let sign = |lit: i32| if lit > 0 { 1i8 } else { -1i8 };
    let lit_value = |value: &[i8], lit: i32| value[lit.unsigned_abs() as usize] * sign(lit);
    for &lit in assumed {
        if lit_value(&value, lit) < 0 {
            return true;
        }
        value[lit.unsigned_abs() as usize] = sign(lit);
    }
    loop {
        let mut changed = false;
        for clause in clauses {
            let mut satisfied = false;
            let mut open = 0usize;
            let mut last_open = 0i32;
            for &lit in clause {
                match lit_value(&value, lit) {
                    v if v > 0 => {
                        satisfied = true;
                        break;
                    }
                    0 => {
                        open += 1;
                        last_open = lit;
                    }
                    _ => {}
                }
            }
            if satisfied {
                continue;
            }
            match open {
                0 => return true,
                1 => {
                    value[last_open.unsigned_abs() as usize] = sign(last_open);
                    changed = true;
                }
                _ => {}
            }
        }
        if !changed {
            return false;
        }
    }
}
