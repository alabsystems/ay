// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Private semantic-test owner. No per-case deadline, ledger or SAT credential.

use super::*;

const MAX_CASE_GATES: usize = 3 * 524_288 + 20 * 4096 + 64;
const MAX_CASES: usize = 90;
const SOURCE_WORK: usize = 100_000_000;
const SOURCE_BYTES: usize = 2_097_152;

// Manual roots have at most three unrolled divisions (NaN self equality),
// twenty other occurrences and two roots. At most V changed UP passes occur:
// each assigns a previously unassigned variable. A final unchanged pass ends.
fn limits(cases: usize) -> (u64, usize) {
    assert!((1..=MAX_CASES).contains(&cases));
    let variables = MAX_CASE_GATES.checked_add(1).unwrap();
    let clauses = MAX_CASE_GATES
        .checked_mul(4)
        .unwrap()
        .checked_add(3)
        .unwrap();
    let scans = variables
        .checked_add(1)
        .unwrap()
        .checked_mul(clauses.checked_mul(5).unwrap().checked_add(1).unwrap())
        .unwrap();
    let scratch = variables
        .checked_mul(std::mem::size_of::<Option<bool>>())
        .unwrap()
        .checked_add(3 * std::mem::size_of::<bool>() + 2 * std::mem::size_of::<Vec<bool>>())
        .unwrap();
    let work = MAX_CASE_GATES
        .checked_mul(1024)
        .unwrap()
        .checked_add(SOURCE_WORK)
        .unwrap()
        .checked_add(scans)
        .unwrap()
        .checked_add(variables + 16)
        .unwrap()
        .checked_mul(cases)
        .unwrap();
    let bytes = MAX_CASE_GATES
        .checked_mul(4096)
        .unwrap()
        .checked_add(SOURCE_BYTES)
        .unwrap()
        .checked_add(scratch)
        .unwrap()
        .checked_mul(cases)
        .unwrap();
    (u64::try_from(work).unwrap(), bytes)
}

pub(super) fn with_owner(cases: usize, run: impl FnOnce(&mut WorkBudget<'_>)) {
    let end = std::time::Instant::now() + std::time::Duration::from_secs(20);
    let (work, storage) = limits(cases); // Checked ONCE before the first case.
    let mut left_work = work;
    let mut left_bytes = storage;
    let mut admission = |units, bytes| {
        if std::time::Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        left_work = left_work
            .checked_sub(u64::try_from(units).unwrap())
            .ok_or(QueryError::Exhausted)?;
        left_bytes = left_bytes.checked_sub(bytes).ok_or(QueryError::Exhausted)?;
        Ok(())
    };
    {
        let mut budget = WorkBudget::with_admission(work, &mut admission);
        budget.charge(0).unwrap();
        run(&mut budget);
        budget.charge(0).unwrap();
    }
    admission(0, 0).unwrap(); // Same captured end after the ledger is dropped.
}

pub(super) fn div(
    terms: &mut TermStore,
    x: TermId,
    y: TermId,
    width: u32,
    rm: RoundingMode,
) -> TermId {
    let (eb, sb) = if width == 32 { (8, 24) } else { (11, 53) };
    let mode = terms.mk_app(
        Symbol::named(rm.name()),
        [],
        Sort::Uninterpreted("RoundingMode".into()),
    );
    terms.mk_app(
        Symbol::named("fp.div"),
        [mode, x, y],
        Sort::FloatingPoint(eb, sb),
    )
}

pub(super) fn constant_roots(
    terms: &TermStore,
    roots: &[TermId],
    budget: &mut WorkBudget<'_>,
) -> Vec<bool> {
    budget.charge(0).unwrap();
    assert!(roots.len() <= 2);
    let plan = source::plan(terms, roots, &[], budget).unwrap();
    assert!(plan.gates >= 524_288 * roots.len());
    assert!(plan.gates <= MAX_CASE_GATES);
    plan.prepay(budget).unwrap();
    let built = encoding::build(terms, roots, &plan, budget).unwrap();
    assert!(built.encoding.cache.next_var as usize - 1 <= plan.gates);
    assert!(built.encoding.clauses.len() <= plan.clauses);
    let variables = built.encoding.cache.next_var as usize;
    let bytes = variables
        .checked_mul(std::mem::size_of::<Option<bool>>())
        .unwrap()
        .checked_add(
            roots.len() * std::mem::size_of::<bool>()
                + std::mem::size_of::<Vec<Option<bool>>>()
                + std::mem::size_of::<Vec<bool>>(),
        )
        .unwrap();
    budget.admit(variables + roots.len() + 2, bytes).unwrap();
    let mut values = vec![None; variables];
    loop {
        budget.charge(1).unwrap();
        let mut changed = false;
        for clause in &built.encoding.clauses {
            budget.charge(1).unwrap();
            assert!(clause.literals().len() <= 4);
            let mut remaining = None;
            let mut count = 0;
            let mut satisfied = false;
            for &lit in clause.literals() {
                budget.charge(1).unwrap();
                match values[lit.unsigned_abs() as usize] {
                    Some(value) if value == (lit > 0) => satisfied = true,
                    Some(_) => {}
                    None => {
                        remaining = Some(lit);
                        count += 1;
                    }
                }
            }
            if !satisfied {
                assert!(count != 0, "complete constant CNF is consistent");
                if count == 1 {
                    let lit = remaining.unwrap();
                    values[lit.unsigned_abs() as usize] = Some(lit > 0);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    let mut result = Vec::with_capacity(roots.len());
    for lit in &built.roots {
        budget.charge(1).unwrap();
        result.push(
            values[lit.unsigned_abs() as usize].expect("constant root determined") == (*lit > 0),
        );
    }
    drop(values);
    drop(built);
    budget.charge(0).unwrap();
    result
}

pub(super) fn word(
    width: u32,
    x: u64,
    y: u64,
    rm: RoundingMode,
    expected: u64,
    budget: &mut WorkBudget<'_>,
) {
    budget.admit(8192, 65_536).unwrap();
    let mut terms = TermStore::new();
    let x = fp_constant(&mut terms, x, width);
    let y = fp_constant(&mut terms, y, width);
    let actual = div(&mut terms, x, y, width, rm);
    let right = fp_constant(&mut terms, expected, width);
    let wrong = fp_constant(&mut terms, expected ^ 1, width);
    let roots = [
        predicate(&mut terms, "=", &[actual, right]),
        predicate(&mut terms, "=", &[actual, wrong]),
    ];
    assert_eq!(
        constant_roots(&terms, &roots, budget),
        [true, false],
        "width{width} {rm:?}"
    );
    drop(terms);
    budget.charge(0).unwrap();
}
