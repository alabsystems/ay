// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Test-only fixed cumulative admission, not a production or RSS allowance.

use super::*;
use ay_sat::{Literal, SatResult, Solver};

const MAX_CASE_GATES: usize = 3 * 917_504 + 24 * 4096 + 64;
const MAX_CASES: usize = 32;
/// The wall end a one-case owner gets. Every owner built on `with_owner` (the
/// remainder and rounded tests) gets it per case, like its work and storage
/// grants. The end only stops a hung case: one binary64 case (planning,
/// construction, propagation and two complete native solves of ~2.7M clauses)
/// takes 2.4-2.6 s on a fast core of the 20-cpu host and 3.8 s on a slow one,
/// so one flat 20 s end for eight such cases raced the clock (19-21 s) and
/// failed host-dependently with `Interrupted(Deadline)`.
const CASE_WALL: Duration = Duration::from_secs(20);

fn limits(cases: usize) -> (u64, usize, Duration) {
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
    let records = variables
        .checked_add(clauses)
        .unwrap()
        .checked_add(4)
        .unwrap();
    let work = MAX_CASE_GATES
        .checked_mul(1024)
        .unwrap()
        .checked_add(scans)
        .unwrap()
        .checked_add(records.checked_mul(128).unwrap())
        .unwrap()
        .checked_add(100_000_000)
        .unwrap()
        .checked_mul(cases)
        .unwrap();
    let bytes = MAX_CASE_GATES
        .checked_mul(4096)
        .unwrap()
        .checked_add(records.checked_mul(1024).unwrap())
        .unwrap()
        .checked_add(8_388_608)
        .unwrap()
        .checked_mul(cases)
        .unwrap();
    let wall = CASE_WALL * u32::try_from(cases).unwrap();
    (u64::try_from(work).unwrap(), bytes, wall)
}

#[test]
fn the_owner_end_is_granted_per_case_like_work_and_storage() {
    let (work, bytes, wall) = limits(1);
    assert_eq!(wall, Duration::from_secs(20));
    for cases in [1, 8, 12, 20, 30, MAX_CASES] {
        let scale = u32::try_from(cases).unwrap();
        assert_eq!(
            limits(cases),
            (work * u64::from(scale), bytes * cases, wall * scale)
        );
    }
    // The owner takes its end from that one grant. Started 30 s ago, three
    // cases still admit (end = start + 60 s); one case, like the old flat 20 s
    // end, has expired and refuses before `run` begins.
    let start = Instant::now().checked_sub(Duration::from_secs(30)).unwrap();
    let mut ran = false;
    let admitted = owner_from(start, 3, |budget| {
        budget.charge(1).unwrap();
        ran = true;
    });
    assert_eq!(admitted, Ok(()));
    assert!(ran);
    let expired = owner_from(start, 1, |_| panic!("a case ran after the end"));
    assert_eq!(expired, Err(QueryError::Interrupted(StopReason::Deadline)));
}

pub(in crate::fp_adapter::tests) fn with_owner(
    cases: usize,
    run: impl FnOnce(&mut WorkBudget<'_>),
) {
    owner_from(Instant::now(), cases, run).unwrap();
}

/// `with_owner` from an explicit start, so the granted end is observable.
fn owner_from(
    start: Instant,
    cases: usize,
    run: impl FnOnce(&mut WorkBudget<'_>),
) -> Result<(), QueryError> {
    let (work, bytes, wall) = limits(cases); // ONE checked grant before the first case.
    let end = start + wall;
    let (mut left_work, mut left_bytes) = (work, bytes);
    let mut admission = |units, storage| {
        if Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        left_work = left_work
            .checked_sub(u64::try_from(units).unwrap())
            .ok_or(QueryError::Exhausted)?;
        left_bytes = left_bytes
            .checked_sub(storage)
            .ok_or(QueryError::Exhausted)?;
        Ok(())
    };
    {
        let mut budget = WorkBudget::with_admission(work, &mut admission);
        budget.charge(0)?;
        run(&mut budget);
        budget.charge(0)?;
    }
    admission(0, 0)
}

pub(super) fn rem(terms: &mut TermStore, x: TermId, y: TermId, width: u32) -> TermId {
    let (eb, sb) = if width == 32 { (8, 24) } else { (11, 53) };
    terms.mk_app(Symbol::named("fp.rem"), [x, y], Sort::FloatingPoint(eb, sb))
}

fn propagate(built: &encoding::Built, budget: &mut WorkBudget<'_>) -> Vec<Option<bool>> {
    let variables = built.encoding.cache.next_var as usize;
    budget
        .admit(
            variables + 1,
            variables
                .checked_mul(std::mem::size_of::<Option<bool>>())
                .unwrap(),
        )
        .unwrap();
    let mut values = vec![None; variables];
    loop {
        budget.charge(1).unwrap();
        let mut changed = false;
        for clause in &built.encoding.clauses {
            budget.charge(1).unwrap();
            let (mut open, mut pending, mut satisfied) = (0, 0, false);
            assert!(clause.literals().len() <= 4);
            for &lit in clause.literals() {
                budget.charge(1).unwrap();
                match values[lit.unsigned_abs() as usize] {
                    Some(value) if value == (lit > 0) => satisfied = true,
                    Some(_) => {}
                    None => {
                        open += 1;
                        pending = lit;
                    }
                }
            }
            if !satisfied {
                assert!(open != 0, "complete constant CNF is consistent");
                if open == 1 {
                    values[pending.unsigned_abs() as usize] = Some(pending > 0);
                    changed = true;
                }
            }
        }
        if !changed {
            return values;
        }
    }
}

fn native(built: &encoding::Built, root: i32, truth: bool, budget: &mut WorkBudget<'_>) {
    let variables = (built.encoding.cache.next_var - 1) as usize;
    let records = variables
        .checked_add(built.encoding.clauses.len())
        .unwrap()
        .checked_add(1)
        .unwrap();
    budget
        .admit(
            records.checked_mul(64).unwrap(),
            records.checked_mul(512).unwrap(),
        )
        .unwrap();
    let mut sat = Solver::new(variables);
    for clause in &built.encoding.clauses {
        budget.charge(1).unwrap();
        let mut row = Vec::with_capacity(clause.literals().len());
        for &lit in clause.literals() {
            budget.charge(1).unwrap();
            row.push(Literal::from_dimacs(lit));
        }
        sat.add_clause(row);
    }
    sat.add_clause(vec![Literal::from_dimacs(root)]);
    let result = {
        let ledger = std::cell::RefCell::new(&mut *budget);
        sat.solve_interruptible(|| ledger.borrow_mut().charge(1).is_err())
            .into_inner()
    };
    match result {
        SatResult::Sat(model) => {
            assert!(truth);
            budget.charge(1).unwrap();
            let value = |lit: i32| model[(lit.unsigned_abs() - 1) as usize] == (lit > 0);
            assert!(value(root));
            for clause in &built.encoding.clauses {
                budget.charge(clause.literals().len() + 1).unwrap();
                assert!(clause.literals().iter().any(|&lit| value(lit)));
            }
        }
        SatResult::Unsat(_) => assert!(!truth),
        _ => panic!("remainder requires a definitive native result"),
    }
    drop(sat);
    budget.charge(0).unwrap();
}

pub(in crate::fp_adapter::tests) fn roots(
    terms: &TermStore,
    roots: &[TermId],
    expected: &[bool],
    budget: &mut WorkBudget<'_>,
) {
    assert_eq!(roots.len(), expected.len());
    assert!(roots.len() <= 2);
    let plan = source::plan(terms, roots, &[], budget).unwrap();
    assert!(plan.gates <= MAX_CASE_GATES);
    plan.prepay(budget).unwrap();
    let built = encoding::build(terms, roots, &plan, budget).unwrap();
    assert!(built.encoding.cache.next_var as usize - 1 <= plan.gates);
    assert!(built.encoding.clauses.len() <= plan.clauses);
    let values = propagate(&built, budget);
    for (&lit, &truth) in built.roots.iter().zip(expected) {
        budget.charge(1).unwrap();
        assert_eq!(
            values[lit.unsigned_abs() as usize],
            Some(truth == (lit > 0))
        );
        native(&built, lit, truth, budget);
    }
    drop((values, built));
    budget.charge(0).unwrap();
}

pub(super) fn word(width: u32, x: u64, y: u64, expected: u64, budget: &mut WorkBudget<'_>) {
    budget.admit(8192, 65_536).unwrap();
    let mut terms = TermStore::new();
    let x = fp_constant(&mut terms, x, width);
    let y = fp_constant(&mut terms, y, width);
    let actual = rem(&mut terms, x, y, width);
    let expected = fp_constant(&mut terms, expected, width);
    let correct = predicate(&mut terms, "=", &[actual, expected]);
    let wrong = terms.mk_not(correct);
    // not(correct) excludes EVERY different SMT word, not just one flipped bit.
    roots(&terms, &[correct, wrong], &[true, false], budget);
    drop(terms);
    budget.charge(0).unwrap();
}
