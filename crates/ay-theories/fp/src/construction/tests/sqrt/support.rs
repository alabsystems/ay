// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One test owner across all cases; not a prospective Sqrt admission fee.

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
    drop(work);
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
    format: (u32, u32),
    mode: RoundingMode,
    input: Word,
    expected: Word,
    work: &mut WorkBudget<'_>,
) {
    let mut terms = TermStore::new();
    let (sqrt, x_term) = root(&mut terms, format.0, format.1, mode);
    let mut stop = |_| work.charge(1).is_err();
    let mut attempt = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
    let result = attempt.try_get_fp(sqrt).unwrap();
    let x = attempt.try_get_fp(x_term).unwrap();
    let mut built = attempt.finish().unwrap();
    drop(stop);
    assert!(!built.has_encoding_gap);
    let cells = (x.exponent.len()
        + x.significand.len()
        + result.exponent.len()
        + result.significand.len()
        + 2)
    .checked_mul(2)
    .unwrap();
    work.admit(
        cells,
        cells.checked_mul(std::mem::size_of::<i32>()).unwrap(),
    )
    .unwrap();
    for lit in signed_bits(&x, input) {
        work.charge(1).unwrap();
        built.clauses.push(CnfClause::unit(lit));
    }
    let correct = signed_bits(&result, expected);
    native(&built, &correct, false, work);
    native(&built, &correct, true, work);
    drop((built, x, result, correct));
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
                .checked_mul(std::mem::size_of::<Literal>())
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
        // A disjunction of all mismatching output bits excludes every wrong
        // word, not merely one chosen perturbation.
        let mut mismatch = Vec::with_capacity(output.len());
        for &lit in output {
            work.charge(1).unwrap();
            mismatch.push(Literal::from_dimacs(-lit));
        }
        sat.add_clause(mismatch);
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
        _ => panic!("complete sqrt native CNF needs a definitive result"),
    }
    drop(sat);
    work.charge(0).unwrap();
}
