// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
struct Prepared(Counted);

#[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
impl Policy for Prepared {
    type Error = CountedAdmissionError;
    fn prepare(&mut self, _: &mut Solver, _: u32, _: Lane) -> Result<(), Self::Error> {
        Ok(())
    }
    #[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
    fn check_frontier(&mut self, s: &mut Solver) {
        self.0.check_frontier(s);
    }
}

#[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
#[test]
fn tight_frontier_appends_and_reason_marks_do_not_grow_inside_committed_kernel() {
    let mut actual = lambda_fixture();
    actual.relevancy_frontier.backtrack_test_shrink();
    for _ in 0..32 {
        actual.arena.add(&[lit(0).negated(), lit(3), lit(7)], true);
    }
    let owner = test_owner(10_000_000, 10_000_000);
    let mut policy = Counted {
        owner: owner.clone(),
        reference: Vec::new(),
    };
    policy
        .prepare(&mut actual, 1, Lane::Standard { save_phases: true })
        .unwrap();
    let frontier_capacity = actual.relevancy_frontier.backtrack_test_capacities();
    let reason_capacity = actual.reason_clause_marks.capacity();
    let reference_capacity = policy.reference.capacity();
    let mut prepared = Prepared(policy);
    actual.backtrack_core(1, true, &mut prepared).unwrap();
    assert_eq!(
        actual.relevancy_frontier.backtrack_test_capacities(),
        frontier_capacity
    );
    assert_eq!(actual.reason_clause_marks.capacity(), reason_capacity);
    assert_eq!(prepared.0.reference.capacity(), reference_capacity);
    assert_eq!(owner.check(), Ok(()));
}

#[test]
fn chained_lambda_reimplication_uses_levels_lowered_earlier_in_real_trail_order() {
    let make = || {
        let mut s = fixture(true, false);
        let first = s.arena.add(&[lit(3), lit(0).negated()], true);
        let second = s.arena.add(&[lit(5), lit(3).negated()], true);
        s.lambda[3] = Some(ClauseRef(first as u32));
        s.lambda[5] = Some(ClauseRef(second as u32));
        s
    };
    let mut expected = make();
    expected.backtrack(1);
    assert_eq!(expected.stats.mli_reimplied, 2);
    assert_eq!(expected.var_data[3].level, 1);
    assert_eq!(expected.var_data[5].level, 1);
    let mut actual = make();
    attach(&mut actual, &test_owner(10_000_000, 10_000_000));
    assert_eq!(actual.backtrack_counted(1), Ok(()));
    assert_eq!(state(&actual), state(&expected));
}

#[test]
fn deleted_and_nonunit_lambda_clauses_still_reinsert_variables() {
    for deleted in [false, true] {
        let make = || {
            let mut s = fixture(true, false);
            // x7 is unassigned: this active clause cannot reimply x3.
            let offset = s.arena.add(&[lit(3), lit(7)], true);
            s.lambda[3] = Some(ClauseRef(offset as u32));
            if deleted {
                s.arena.delete(offset);
            }
            s
        };
        let mut expected = make();
        expected.backtrack(1);
        assert_eq!(expected.stats.mli_reimplied, 0);
        assert_eq!(expected.vals[lit(3).index()], 0);
        assert!(expected.vsids.bucket_queue_contains(Variable(3)));
        let mut actual = make();
        attach(&mut actual, &test_owner(10_000_000, 10_000_000));
        assert_eq!(actual.backtrack_counted(1), Ok(()));
        assert_eq!(state(&actual), state(&expected));
    }
}

#[test]
fn long_active_lambda_edges_are_paid_even_when_reimplication_fails() {
    let make = |length| {
        let mut s = fixture(true, false);
        // Repeated falsified literal occurrences deliberately force the real
        // lambda scan through every edge before the final unassigned literal.
        let mut clause = vec![lit(0).negated(); length];
        clause.push(lit(3));
        clause.push(lit(7));
        let offset = s.arena.add(&clause, true);
        s.lambda[3] = Some(ClauseRef(offset as u32));
        s.relevancy_frontier.invalidate();
        s
    };
    let used = |length| {
        let mut s = make(length);
        let owner = test_owner(10_000_000, 10_000_000);
        attach(&mut s, &owner);
        assert_eq!(s.backtrack_counted(1), Ok(()));
        owner.usage().unwrap().work_admitted
    };
    assert!(used(1024) >= used(8) + 1016);
    let mut s = make(1024);
    let before = state(&s);
    attach(&mut s, &test_owner(used(8), 10_000_000));
    assert_eq!(
        s.backtrack_counted(1),
        Err(SatUnknownReason::ResourceBudget)
    );
    assert_eq!(state(&s), before);
}

#[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
#[test]
fn frontier_unassignment_debit_is_linear_for_one_shared_long_clause() {
    let used = |n: u32| {
        let mut s = Solver::new(n as usize);
        for index in 0..n {
            s.qhead = s.trail.len();
            s.decide(lit(index));
        }
        s.qhead = s.trail.len();
        let clause: Vec<_> = (0..n).map(lit).collect();
        s.arena.add(&clause, false);
        sync_frontier(&mut s);
        let owner = test_owner(10_000_000, 10_000_000);
        attach(&mut s, &owner);
        assert_eq!(s.backtrack_counted(0), Ok(()));
        owner.usage().unwrap().work_admitted
    };
    let small = used(64);
    let large = used(128);
    assert!(large > small);
    assert!(
        large < 3 * small,
        "shared-clause cost must not become quadratic"
    );
}
