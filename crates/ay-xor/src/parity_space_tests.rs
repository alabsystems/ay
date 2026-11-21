// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Tests for the parity-space walk (AY-SAT-2).

use super::*;

fn lit(var: u32, positive: bool) -> Literal {
    literal(var, positive)
}

/// The full CNF encoding of `XOR(vars) = rhs`: one clause per assignment of
/// the wrong parity.
fn xor_clauses(vars: &[u32], rhs: bool) -> Vec<Vec<Literal>> {
    let n = vars.len();
    let mut clauses = Vec::new();
    for assignment in 0u32..(1 << n) {
        let parity = assignment.count_ones() % 2 == 1;
        if parity == rhs {
            continue;
        }
        // Forbid `assignment`: each literal is false under it.
        clauses.push(
            vars.iter()
                .enumerate()
                .map(|(index, &var)| lit(var, (assignment >> index) & 1 == 0))
                .collect(),
        );
    }
    clauses
}

/// Sinz sequential counter for "at most `k` of `inputs` are true", with
/// registers allocated from `next_var`. Register literals come first in each
/// clause, as the greedy completion prefers negative literals.
fn at_most(inputs: &[u32], k: usize, next_var: &mut u32) -> Vec<Vec<Literal>> {
    let n = inputs.len();
    let mut registers = vec![vec![0u32; k]; n];
    for row in registers.iter_mut() {
        for slot in row.iter_mut() {
            *slot = *next_var;
            *next_var += 1;
        }
    }
    let mut clauses = Vec::new();
    for (i, &x) in inputs.iter().enumerate() {
        clauses.push(vec![lit(x, false), lit(registers[i][0], true)]);
        if i > 0 {
            for j in 0..k {
                clauses.push(vec![
                    lit(registers[i - 1][j], false),
                    lit(registers[i][j], true),
                ]);
            }
            for j in 1..k {
                clauses.push(vec![
                    lit(registers[i - 1][j - 1], false),
                    lit(x, false),
                    lit(registers[i][j], true),
                ]);
            }
            clauses.push(vec![lit(registers[i - 1][k - 1], false), lit(x, false)]);
        }
    }
    clauses
}

fn never_stop() -> bool {
    false
}

#[test]
fn a_pure_xor_chain_is_solved_with_a_checked_model() {
    // x0 ^ x1 ^ x2 = 1, x2 ^ x3 ^ x4 = 0, x4 ^ x5 ^ x6 = 1: dimension 4.
    let mut clauses = xor_clauses(&[0, 1, 2], true);
    clauses.extend(xor_clauses(&[2, 3, 4], false));
    clauses.extend(xor_clauses(&[4, 5, 6], true));
    let (outcome, stats) = solve_parity_space(7, &clauses, &never_stop);
    let ParitySpaceOutcome::Model(model) = outcome else {
        panic!("expected a model, got {outcome:?}");
    };
    assert_eq!(model.len(), 7);
    assert!(model_satisfies(&model, &clauses));
    assert_eq!(stats.rank, 3);
    assert_eq!(stats.dimension, 4);
    assert_eq!(stats.weight_filter, None);
}

#[test]
fn a_ternary_xor_chain_with_residual_binaries_is_solved() {
    // The 7db30d12 shape at a small size: a chain of ternary XORs
    // x_i ^ x_{i+1} ^ y_i (13 columns x, 12 columns y, rank 12, dimension 13)
    // plus binary clauses over XOR variables that only some points satisfy.
    let mut clauses = Vec::new();
    for i in 0..12u32 {
        clauses.extend(xor_clauses(&[i, i + 1, i + 13], i % 3 == 0));
    }
    clauses.push(vec![lit(0, false), lit(1, false)]);
    clauses.push(vec![lit(5, true), lit(20, false)]);
    let (outcome, stats) = solve_parity_space(25, &clauses, &never_stop);
    let ParitySpaceOutcome::Model(model) = outcome else {
        panic!("expected a model, got {outcome:?}");
    };
    assert!(model_satisfies(&model, &clauses));
    assert_eq!(stats.xors, 12);
    assert_eq!(stats.residual_clauses, 2);
    assert_eq!(stats.dimension, 13);
}

#[test]
fn a_supported_partial_xor_is_recovered_and_its_binary_respected() {
    // XOR(0, 1, 2) = 1 encoded by three of its four clauses; the fourth,
    // (x0 | x1 | x2), is subsumed by the binary (x0 | x1).
    let mut clauses: Vec<Vec<Literal>> = xor_clauses(&[0, 1, 2], true)
        .into_iter()
        .filter(|clause| clause.iter().any(|lit| !lit.is_positive()))
        .collect();
    assert_eq!(clauses.len(), 3);
    clauses.push(vec![lit(0, true), lit(1, true)]);
    clauses.extend(xor_clauses(&[2, 3, 4], false));
    let (outcome, _) = solve_parity_space(5, &clauses, &never_stop);
    let ParitySpaceOutcome::Model(model) = outcome else {
        panic!("expected a model, got {outcome:?}");
    };
    assert!(model_satisfies(&model, &clauses));
}

#[test]
fn an_inconsistent_system_is_declined_not_claimed() {
    let mut clauses = xor_clauses(&[0, 1], true);
    clauses.extend(xor_clauses(&[1, 2], true));
    clauses.extend(xor_clauses(&[0, 2], true));
    let (outcome, _) = solve_parity_space(3, &clauses, &never_stop);
    assert_eq!(
        outcome,
        ParitySpaceOutcome::Declined(ParitySpaceDecline::Inconsistent)
    );
}

/// x0 ^ x1 = 1 and x1 ^ x2 = 1 force x0 = x2; the residual is the two unit
/// clauses x0 and -x2, which no point satisfies. Units are not XORs to the
/// finder (two literals at least), so they stay in the residual. (A residual of
/// (x0 | x2) and (-x0 | -x2) would not do: that pair is the full encoding of
/// x0 ^ x2 = 1, which the finder takes as a third XOR.)
fn space_without_a_model() -> Vec<Vec<Literal>> {
    let mut clauses = xor_clauses(&[0, 1], true);
    clauses.extend(xor_clauses(&[1, 2], true));
    clauses.push(vec![lit(0, true)]);
    clauses.push(vec![lit(2, false)]);
    clauses
}

#[test]
fn a_residual_no_point_satisfies_is_declined_not_claimed() {
    let clauses = space_without_a_model();
    let (outcome, stats) = solve_parity_space(3, &clauses, &never_stop);
    assert_eq!(
        outcome,
        ParitySpaceOutcome::Declined(ParitySpaceDecline::NoModelFound)
    );
    assert_eq!(stats.xors, 2);
    assert_eq!(stats.residual_clauses, 2);
    assert_eq!(stats.dimension, 1);
    assert_eq!(stats.points, 2);
    assert_eq!(stats.candidates, 2);
}

#[test]
fn a_formula_without_xors_is_declined() {
    let clauses = vec![vec![lit(0, true), lit(1, true), lit(2, true)]];
    let (outcome, _) = solve_parity_space(3, &clauses, &never_stop);
    assert_eq!(
        outcome,
        ParitySpaceOutcome::Declined(ParitySpaceDecline::NoXor)
    );
}

/// The db15a856 shape at a small size: 20 secret bits, 40 parities of them,
/// and "at most 3 parities are 1" over the parity outputs.
fn minimum_disagreement_instance() -> (u32, Vec<Vec<Literal>>) {
    let secret: u32 = 0b1011_0010_1110_0101_1001;
    let mut rng = SplitMix64(7);
    let mut clauses = Vec::new();
    let outputs: Vec<u32> = (20..60).collect();
    let errors = [3usize, 17, 31];
    for (index, &output) in outputs.iter().enumerate() {
        // output ^ a ^ b ^ c = rhs, with the planted secret giving output = error bit.
        let mut picks = Vec::new();
        while picks.len() < 3 {
            let var = (rng.next_u64() % 20) as u32;
            if !picks.contains(&var) {
                picks.push(var);
            }
        }
        let parity = picks
            .iter()
            .fold(false, |acc, &var| acc ^ ((secret >> var) & 1 == 1));
        let rhs = parity ^ errors.contains(&index);
        let mut vars = picks;
        vars.push(output);
        clauses.extend(xor_clauses(&vars, rhs));
    }
    let mut next_var = 60;
    clauses.extend(at_most(&outputs, 3, &mut next_var));
    (next_var, clauses)
}

#[test]
fn a_cardinality_bound_over_parities_is_walked_with_a_weight_filter() {
    let (num_vars, clauses) = minimum_disagreement_instance();
    let (outcome, stats) = solve_parity_space(num_vars as usize, &clauses, &never_stop);
    let ParitySpaceOutcome::Model(model) = outcome else {
        panic!("expected a model, got {outcome:?} with {stats:?}");
    };
    assert!(model_satisfies(&model, &clauses));
    assert!(stats.dimension > FULL_SCAN_MAX_DIMENSION, "{stats:?}");
    assert_eq!(stats.weight_filter, Some((true, 3)));
    let weight = (20..60).filter(|&var| model[var]).count();
    assert!(weight <= 3);
}

#[test]
fn a_stop_request_before_the_walk_answers_stopped() {
    // The walk would find a model at once; a stop already requested wins.
    let mut clauses = xor_clauses(&[0, 1, 2], true);
    clauses.extend(xor_clauses(&[2, 3, 4], false));
    let (outcome, stats) = solve_parity_space(5, &clauses, &|| true);
    assert_eq!(
        outcome,
        ParitySpaceOutcome::Declined(ParitySpaceDecline::Stopped)
    );
    assert_eq!(stats.candidates, 0);
}

#[test]
fn a_stop_request_during_a_full_scan_answers_stopped() {
    // Two points, neither a model. The stop comes at the fourth poll: after the
    // recovery (1), the walk's poll at point 0 (2) and the first candidate's
    // poll (3), so at the second candidate. Without a per-candidate poll a walk
    // this short never polls and ends NoModelFound.
    let clauses = space_without_a_model();
    let polls = std::cell::Cell::new(0u32);
    let stop = || {
        polls.set(polls.get() + 1);
        polls.get() >= 4
    };
    let (outcome, stats) = solve_parity_space(3, &clauses, &stop);
    assert_eq!(
        outcome,
        ParitySpaceOutcome::Declined(ParitySpaceDecline::Stopped)
    );
    assert_eq!(polls.get(), 4);
    assert_eq!(stats.candidates, 1);
}

#[test]
fn a_stop_request_during_a_filtered_walk_answers_stopped() {
    // A stop requested from the start ends the route right after the XORs are
    // recovered, before the probe and the walk, whatever the instance.
    let (num_vars, clauses) = minimum_disagreement_instance();
    let (outcome, stats) = solve_parity_space(num_vars as usize, &clauses, &|| true);
    assert_eq!(
        outcome,
        ParitySpaceOutcome::Declined(ParitySpaceDecline::Stopped)
    );
    assert_eq!(stats.candidates, 0);
    // Stopping at the fourth poll falls inside the probe, which polls once per
    // sample, and gives the same answer.
    let polls = std::cell::Cell::new(0u32);
    let stop = || {
        polls.set(polls.get() + 1);
        polls.get() > 3
    };
    let (outcome, _) = solve_parity_space(num_vars as usize, &clauses, &stop);
    assert_eq!(
        outcome,
        ParitySpaceOutcome::Declined(ParitySpaceDecline::Stopped)
    );
}

#[test]
fn one_completion_scans_the_residual_a_bounded_number_of_times() {
    // n independent clauses (x_2i | x_2i+1): each needs a greedy choice. The
    // cursor visits each clause twice (open, then satisfied); rescanning from
    // the first clause after every choice would visit about n^2 / 2.
    let n = 2000u32;
    let clauses: Vec<Vec<Literal>> = (0..n)
        .map(|i| vec![lit(2 * i, true), lit(2 * i + 1, true)])
        .collect();
    let residual: Vec<&[Literal]> = clauses.iter().map(Vec::as_slice).collect();
    let mut evaluator = ResidualEvaluator::new(2 * n as usize, residual);
    assert!(evaluator.reset_and_start());
    assert!(evaluator.complete());
    let scanned = evaluator.scanned;
    assert!(scanned <= 2 * u64::from(n) + 1, "{scanned}");
    let model: Vec<bool> = (0..2 * n as usize)
        .map(|var| evaluator.value(var).unwrap_or(false))
        .collect();
    assert!(model_satisfies(&model, &clauses));
    // A second completion after a reset starts from the first clause again.
    assert!(evaluator.reset_and_start());
    assert!(evaluator.complete());
    let again: Vec<bool> = (0..2 * n as usize)
        .map(|var| evaluator.value(var).unwrap_or(false))
        .collect();
    assert!(model_satisfies(&again, &clauses));
}
