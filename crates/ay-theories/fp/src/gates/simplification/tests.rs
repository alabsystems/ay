// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{CnfClause, TermStore};

mod ownership;

type TestResult<T = ()> = Result<T, Box<dyn std::error::Error>>;

#[derive(Clone, Copy, Debug)]
enum Binary {
    And,
    Or,
    Xor,
}

impl Binary {
    fn build(self, solver: &mut FpSolver<'_>, a: CnfLit, b: CnfLit) -> CnfLit {
        match self {
            Self::And => solver.make_and(a, b),
            Self::Or => solver.make_or(a, b),
            Self::Xor => solver.make_xor(a, b),
        }
    }

    fn value(self, a: bool, b: bool) -> bool {
        match self {
            Self::And => a && b,
            Self::Or => a || b,
            Self::Xor => a ^ b,
        }
    }

    fn old_clauses(self) -> usize {
        match self {
            Self::And | Self::Or => 3,
            Self::Xor => 4,
        }
    }
}

fn value(assignment: usize, lit: CnfLit) -> TestResult<bool> {
    let var_index = lit
        .unsigned_abs()
        .checked_sub(1)
        .ok_or("literal 0 names no variable")?;
    let var_mask = 1usize
        .checked_shl(var_index)
        .ok_or_else(|| format!("literal {lit} is beyond the assignment's bits"))?;
    let bit = assignment & var_mask != 0;
    Ok(if lit > 0 { bit } else { !bit })
}

/// Enumerate every complete CNF assignment, including auxiliary variables.
/// Each input assignment must extend to a model, and every such model must
/// satisfy the claimed relation. This tests both directions without SAT search.
fn check_cnf(
    vars: u32,
    clauses: &[CnfClause],
    free_inputs: u32,
    relation: impl Fn(usize) -> TestResult<bool>,
) -> TestResult {
    if vars >= 16 {
        return Err(format!("{vars} variables are too many to enumerate").into());
    }
    // The free inputs are the first variables, so there are at most `vars`.
    if free_inputs > vars {
        return Err(format!("{free_inputs} free inputs among {vars} variables").into());
    }
    let input_count = 1usize
        .checked_shl(free_inputs)
        .ok_or("free-input count overflow")?;
    let input_mask = input_count.checked_sub(1).ok_or("empty input space")?;
    let model_count = 1usize
        .checked_shl(vars)
        .ok_or("assignment count overflow")?;
    let mut seen = vec![false; input_count];
    for assignment in 0..model_count {
        let mut satisfied = true;
        for clause in clauses {
            let mut clause_true = false;
            for &lit in clause.literals() {
                if value(assignment, lit)? {
                    clause_true = true;
                    break;
                }
            }
            if !clause_true {
                satisfied = false;
                break;
            }
        }
        if satisfied {
            if !relation(assignment)? {
                return Err(format!("wrong CNF model {assignment:b}").into());
            }
            *seen
                .get_mut(assignment & input_mask)
                .ok_or("input index out of range")? = true;
        }
    }
    if !seen.into_iter().all(|present| present) {
        return Err("missing input model".into());
    }
    Ok(())
}

fn inputs(solver: &mut FpSolver<'_>) -> [CnfLit; 10] {
    let a = solver.fresh_var();
    let b = solver.fresh_var();
    let c = solver.fresh_var();
    let f = solver.const_false();
    let t = solver.const_true();
    [a, -a, b, -b, c, -c, f, -f, t, -t]
}

#[test]
fn all_binary_literal_and_constant_combinations_have_exact_cnf() -> TestResult {
    let terms = TermStore::new();
    for gate in [Binary::And, Binary::Or, Binary::Xor] {
        for i in 0..10 {
            for j in 0..10 {
                let mut solver = FpSolver::new(&terms);
                let literals = inputs(&mut solver);
                let a = *literals.get(i).ok_or("input index out of range")?;
                let b = *literals.get(j).ok_or("input index out of range")?;
                let before = (solver.num_vars(), solver.clauses().len());
                let out = gate.build(&mut solver, a, b);
                let max_vars = before.0.checked_add(1).ok_or("variable count overflow")?;
                let max_clauses = before
                    .1
                    .checked_add(gate.old_clauses())
                    .ok_or("clause count overflow")?;
                assert!(solver.num_vars() <= max_vars);
                assert!(solver.clauses().len() <= max_clauses);
                check_cnf(solver.num_vars(), solver.clauses(), 3, |bits| {
                    Ok(value(bits, out)? == gate.value(value(bits, a)?, value(bits, b)?))
                })?;
            }
        }
    }
    Ok(())
}

#[test]
fn all_ite_literal_and_constant_combinations_have_exact_cnf() -> TestResult {
    let terms = TermStore::new();
    for i in 0..10 {
        for j in 0..10 {
            for k in 0..10 {
                let mut solver = FpSolver::new(&terms);
                let literals = inputs(&mut solver);
                let cond = *literals.get(i).ok_or("input index out of range")?;
                let yes = *literals.get(j).ok_or("input index out of range")?;
                let no = *literals.get(k).ok_or("input index out of range")?;
                let before = (solver.num_vars(), solver.clauses().len());
                let out = solver.make_ite(cond, yes, no);
                let max_vars = before.0.checked_add(1).ok_or("variable count overflow")?;
                let max_clauses = before.1.checked_add(4).ok_or("clause count overflow")?;
                assert!(solver.num_vars() <= max_vars);
                assert!(solver.clauses().len() <= max_clauses);
                check_cnf(solver.num_vars(), solver.clauses(), 3, |bits| {
                    let expected = if value(bits, cond)? { yes } else { no };
                    Ok(value(bits, out)? == value(bits, expected)?)
                })?;
            }
        }
    }
    Ok(())
}

#[test]
fn distinct_symbolic_inputs_keep_the_original_gate_counts() -> TestResult {
    let terms = TermStore::new();
    for polarity in 0..8 {
        for gate in [Binary::And, Binary::Or, Binary::Xor] {
            let mut solver = FpSolver::new(&terms);
            let a = solver.fresh_var();
            let b = solver.fresh_var();
            let a = if polarity & 1 == 0 { a } else { -a };
            let b = if polarity & 2 == 0 { b } else { -b };
            let out = gate.build(&mut solver, a, b);
            assert_eq!(solver.num_vars(), 3);
            assert_eq!(solver.clauses().len(), gate.old_clauses());
            check_cnf(3, solver.clauses(), 2, |bits| {
                Ok(value(bits, out)? == gate.value(value(bits, a)?, value(bits, b)?))
            })?;
        }
        let mut solver = FpSolver::new(&terms);
        let mut literals = [solver.fresh_var(), solver.fresh_var(), solver.fresh_var()];
        // Bit `i` of `polarity` negates literal `i`.
        for (polarity_bit, lit) in [1, 2, 4].into_iter().zip(literals.iter_mut()) {
            if polarity & polarity_bit != 0 {
                *lit = -*lit;
            }
        }
        let [cond, yes, no] = literals;
        let out = solver.make_ite(cond, yes, no);
        assert_eq!((solver.num_vars(), solver.clauses().len()), (4, 4));
        check_cnf(4, solver.clauses(), 3, |bits| {
            Ok(value(bits, out)? == value(bits, if value(bits, cond)? { yes } else { no })?)
        })?;
    }
    Ok(())
}

#[test]
fn complement_identities_create_real_pinned_constants_when_needed() -> TestResult {
    let terms = TermStore::new();
    for gate in [Binary::And, Binary::Or, Binary::Xor] {
        let mut solver = FpSolver::new(&terms);
        let a = solver.fresh_var();
        let not_a = a.checked_neg().ok_or("fresh variable has no negation")?;
        let out = gate.build(&mut solver, a, not_a);
        assert_eq!((solver.num_vars(), solver.clauses().len()), (2, 1));
        check_cnf(2, solver.clauses(), 1, |bits| {
            Ok(value(bits, out)? == gate.value(value(bits, a)?, !value(bits, a)?))
        })?;
    }
    Ok(())
}

#[test]
fn padded_addition_reuses_input_bits_without_new_gates() -> TestResult {
    let terms = TermStore::new();
    for width in [1, 8, 53, 113] {
        let mut solver = FpSolver::new(&terms);
        let mut bits = Vec::new();
        bits.try_reserve_exact(width)?;
        for _ in 0..width {
            bits.push(solver.fresh_var());
        }
        let zero = solver.const_bv(0, width);
        let before = (solver.num_vars(), solver.clauses().len());
        assert_eq!(solver.bv_add(&bits, &zero), bits);
        assert_eq!((solver.num_vars(), solver.clauses().len()), before);
        // The old full-adder roster emitted 2 XOR + 2 AND + 1 OR per bit.
        let old_roster = width
            .checked_mul(17)
            .and_then(|clauses| clauses.checked_add(1))
            .ok_or("old roster size overflow")?;
        assert!(solver.clauses().len() < old_roster);
    }
    Ok(())
}

#[test]
fn symbolic_two_bit_addition_is_exact_and_smaller_than_old_roster() -> TestResult {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = [solver.fresh_var(), solver.fresh_var()];
    let b = [solver.fresh_var(), solver.fresh_var()];
    let sum = solver.bv_add(&a, &b);
    assert!(solver.clauses().len() < 1 + 17 * 2);
    check_cnf(solver.num_vars(), solver.clauses(), 4, |bits| {
        let read = |v: &[CnfLit]| -> TestResult<usize> {
            let [lo, hi] = v else {
                return Err(format!("{}-bit value, expected 2 bits", v.len()).into());
            };
            Ok(usize::from(value(bits, *lo)?) + 2 * usize::from(value(bits, *hi)?))
        };
        let total = read(&a)?.checked_add(read(&b)?).ok_or("sum overflow")?;
        Ok(read(&sum)? == total % 4)
    })?;
    Ok(())
}
