// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One test-only grant/end for all cases; not a production FMA fee.

use super::*;
use ay_core::original_query::{QueryError, StopReason, WorkBudget};
use ay_core::CnfClause;
use ay_sat::{Literal, SatResult, Solver};

pub(super) type Word = (bool, u64, u64);

pub(super) fn with_owner(run: impl FnOnce(&mut WorkBudget<'_>)) {
    let end = Instant::now() + Duration::from_secs(20);
    let (mut units_left, mut bytes_left) = (100_000_000u64, 536_870_912usize);
    let mut original = |units: usize, bytes: usize| {
        if Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        units_left = units_left
            .checked_sub(u64::try_from(units).unwrap())
            .ok_or(QueryError::Exhausted)?;
        bytes_left = bytes_left.checked_sub(bytes).ok_or(QueryError::Exhausted)?;
        Ok(())
    };
    let mut work = WorkBudget::with_admission(100_000_000, &mut original);
    work.charge(0).unwrap();
    run(&mut work);
    work.charge(0).unwrap();
    original(0, 0).unwrap();
}

fn signed_bits(fp: &FpDecomposed, (sign, exp, sig): Word) -> Vec<i32> {
    std::iter::once(if sign { fp.sign } else { -fp.sign })
        .chain(fp.exponent.iter().enumerate().map(
            |(i, &lit)| {
                if (exp >> i) & 1 == 1 {
                    lit
                } else {
                    -lit
                }
            },
        ))
        .chain(fp.significand.iter().enumerate().map(
            |(i, &lit)| {
                if (sig >> i) & 1 == 1 {
                    lit
                } else {
                    -lit
                }
            },
        ))
        .collect()
}

pub(super) fn case(
    mode: RoundingMode,
    inputs: [Word; 3],
    expected: Word,
    work: &mut WorkBudget<'_>,
) {
    work.admit(128, 4096).unwrap(); // bounded term descriptors before fixture construction
    let mut terms = TermStore::new();
    let (fma, source) = root(&mut terms, 5, 11, mode);
    let mut stop = |_| work.charge(1).is_err();
    let mut attempt = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
    let result = attempt.try_get_fp(fma).unwrap();
    let values = source.map(|term| attempt.try_get_fp(term).unwrap());
    let mut built = attempt.finish().unwrap();
    drop(stop);
    assert!(!built.has_encoding_gap);
    let cells = (values
        .iter()
        .map(|v| v.exponent.len() + v.significand.len() + 1)
        .sum::<usize>()
        + result.exponent.len()
        + result.significand.len()
        + 1)
    .checked_mul(2)
    .unwrap();
    work.admit(cells, cells.checked_mul(size_of::<i32>()).unwrap())
        .unwrap();
    let units = values
        .iter()
        .map(|v| v.exponent.len() + v.significand.len() + 1)
        .sum::<usize>();
    let moved = built
        .clauses
        .len()
        .checked_mul(2)
        .unwrap()
        .checked_add(units)
        .unwrap();
    work.admit(moved, moved.checked_mul(size_of::<CnfClause>()).unwrap())
        .unwrap();
    built.clauses.try_reserve_exact(units).unwrap();
    for (value, bits) in values.iter().zip(inputs) {
        for lit in signed_bits(value, bits) {
            work.admit(1, size_of::<CnfClause>() + size_of::<i32>())
                .unwrap();
            built.clauses.push(CnfClause::unit(lit));
        }
    }
    let correct = signed_bits(&result, expected);
    native(&built, &correct, false, work);
    native(&built, &correct, true, work);
    drop((built, values, result, correct));
    work.charge(0).unwrap();
}

fn native(built: &FpBuiltEncoding, output: &[i32], wrong: bool, work: &mut WorkBudget<'_>) {
    let records = (built.cache.next_var as usize)
        .checked_add(built.clauses.len())
        .unwrap()
        .checked_add(output.len() + 1)
        .unwrap();
    work.admit(
        records.checked_mul(128).unwrap(),
        records.checked_mul(512).unwrap(),
    )
    .unwrap();
    let mut sat = Solver::new((built.cache.next_var - 1) as usize);
    for clause in &built.clauses {
        work.admit(
            clause.literals().len() + 1,
            clause
                .literals()
                .len()
                .checked_mul(size_of::<Literal>())
                .unwrap(),
        )
        .unwrap();
        let mut row = Vec::with_capacity(clause.literals().len());
        for &lit in clause.literals() {
            work.charge(1).unwrap();
            row.push(Literal::from_dimacs(lit));
        }
        sat.add_clause(row);
    }
    if wrong {
        let mut mismatch = Vec::with_capacity(output.len());
        for &lit in output {
            work.charge(1).unwrap();
            mismatch.push(Literal::from_dimacs(-lit));
        }
        sat.add_clause(mismatch); // disjunction of ALL incorrect output bits
    } else {
        for &lit in output {
            work.charge(1).unwrap();
            sat.add_clause(vec![Literal::from_dimacs(lit)]);
        }
    }
    let result = {
        let ledger = RefCell::new(&mut *work);
        sat.solve_interruptible(|| ledger.borrow_mut().charge(1).is_err())
            .into_inner()
    };
    match result {
        SatResult::Sat(model) => {
            assert!(!wrong);
            let value = |lit: i32| model[(lit.unsigned_abs() - 1) as usize] == (lit > 0);
            for &lit in output {
                work.charge(1).unwrap();
                assert!(value(lit));
            }
            for clause in &built.clauses {
                work.charge(clause.literals().len() + 1).unwrap();
                assert!(clause.literals().iter().any(|&lit| value(lit)));
            }
        }
        SatResult::Unsat(_) => assert!(wrong),
        _ => panic!("complete FMA native CNF needs a definitive result"),
    }
    drop(sat);
    work.charge(0).unwrap();
}
