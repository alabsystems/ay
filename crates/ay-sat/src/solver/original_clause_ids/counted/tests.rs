// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
use super::*;
use crate::counted_storage::test_owner;

fn fixture() -> (Solver, CountedInitialCnf, CountedAdmission) {
    let _ = ay_core::misc_cli_flags();
    let owner = test_owner(100_000_000, 100_000_000);
    let input = CountedInitialCnf::try_new(2, &[&[Literal(0), Literal(2)]], owner.clone()).unwrap();
    // This test isolates registration. The production constructor, separately
    // tested, pays the actual construction/arming before reaching this method.
    let mut solver = Solver::new(2);
    solver.enable_clause_trace();
    solver.attach_counted_admission(owner.clone()).unwrap();
    (solver, input, owner)
}

#[test]
fn exclusive_original_session_refuses_collisions_derived_ids_and_foreign_owners() {
    for mutation in 0..5 {
        let (mut s, input, owner) = fixture();
        match mutation {
            0 => s.cold.next_clause_id = 2,
            1 => {
                s.cold
                    .clause_trace
                    .as_mut()
                    .unwrap()
                    .add_clause_with_hint_slices(1, &[Literal(0)], false, &[]);
            }
            2 => {
                s.add_clause(vec![Literal(0)]);
            }
            3 => s.cold.counted_admission = Some(test_owner(100_000_000, 100_000_000)),
            _ => s.cold.next_original_clause_id = u64::MAX,
        }
        let before = (
            s.arena.num_clauses(),
            s.cold.original_ledger.num_clauses(),
            s.cold.clause_trace.as_ref().unwrap().entries().len(),
        );
        assert!(
            install(&mut s, &input, &owner).is_err(),
            "mutation {mutation}"
        );
        assert_eq!(
            before,
            (
                s.arena.num_clauses(),
                s.cold.original_ledger.num_clauses(),
                s.cold.clause_trace.as_ref().unwrap().entries().len()
            )
        );
        assert!(owner.usage().unwrap().refusal.is_some());
    }
}

#[test]
fn a_consumed_registration_session_cannot_be_reopened_as_fresh_originals() {
    let (mut s, input, owner) = fixture();
    let first = install(&mut s, &input, &owner).unwrap();
    assert_eq!(first.ids, [Some(1)]);
    let before = s.cold.next_clause_id;
    assert!(install(&mut s, &input, &owner).is_err());
    assert_eq!(s.cold.next_clause_id, before);
    assert_eq!(s.cold.original_ledger.clause_ids(), &[1]);
}

fn registration_work(count: usize) -> u64 {
    let _ = ay_core::misc_cli_flags();
    let owner = test_owner(1_000_000_000, 1_000_000_000);
    let clauses: Vec<_> = (0..count).map(|_| &[Literal(0), Literal(2)][..]).collect();
    let input = CountedInitialCnf::try_new(2, &clauses, owner.clone()).unwrap();
    let mut s = Solver::with_clause_hint(2, count);
    s.enable_clause_trace();
    s.attach_counted_admission(owner.clone()).unwrap();
    let before = owner.usage().unwrap().work_admitted;
    let installed = install(&mut s, &input, &owner).unwrap();
    assert_eq!(installed.ids.len(), count);
    assert_eq!(installed.ids.last(), Some(&Some(count as u64)));
    assert_eq!(s.cold.clause_trace.as_ref().unwrap().entries().len(), count);
    assert_eq!(
        s.cold.original_ledger.clause_ids().last(),
        Some(&(count as u64))
    );
    owner.usage().unwrap().work_admitted - before
}

#[test]
fn actual_fresh_original_trace_registration_has_no_quadratic_prior_id_scan() {
    let work: Vec<_> = [128, 256, 512].into_iter().map(registration_work).collect();
    assert!(work[0] > 128 && work[1] > work[0] && work[2] > work[1]);
    for pair in work.windows(2) {
        assert!(pair[1] < pair[0] * 3, "{work:?}");
    }
    // This is the actual registration kernel, not a claim that unrelated
    // constructor, watch building, or complete solving is asymptotically linear.
}

#[test]
fn real_tautology_gaps_and_empty_publications_do_not_reintroduce_quadratic_id_checks() {
    let work: Vec<_> = [64, 128, 256]
        .into_iter()
        .map(|count| {
            let _ = ay_core::misc_cli_flags();
            let owner = test_owner(1_000_000_000, 1_000_000_000);
            let clauses: Vec<_> = (0..count)
                .map(|i| match i % 3 {
                    0 => &[Literal(0), Literal(1)][..],
                    1 => &[][..],
                    _ => &[Literal(0), Literal(2)][..],
                })
                .collect();
            let input = CountedInitialCnf::try_new(2, &clauses, owner.clone()).unwrap();
            let mut s = Solver::with_clause_hint(2, count);
            s.enable_clause_trace();
            s.attach_counted_admission(owner.clone()).unwrap();
            let before = owner.usage().unwrap().work_admitted;
            let installed = install(&mut s, &input, &owner).unwrap();
            assert_eq!(installed.ids.len(), count);
            assert!(s.cold.next_clause_id > count as u64);
            owner.usage().unwrap().work_admitted - before
        })
        .collect();
    assert!(work[0] > 0);
    for pair in work.windows(2) {
        assert!(pair[1] > pair[0] && pair[1] < pair[0] * 3, "{work:?}");
    }
}

#[test]
fn fresh_token_rejects_a_corrupt_or_derived_trace_prefix_without_publication() {
    for corrupt in 0..3 {
        let (mut s, _, owner) = fixture();
        let mut session = Fresh::new(&mut s, &owner).unwrap();
        assert_eq!(session.append(&[Literal(0), Literal(2)]).unwrap(), 1);
        let trace = session.solver.cold.clause_trace.as_mut().unwrap();
        if corrupt == 0 {
            trace.add_clause_with_hint_slices(2, &[Literal(0)], false, &[]);
        } else if corrupt == 1 {
            trace.mark_proof_work_exhausted();
        } else {
            trace.add_clause_with_hint_slices(u64::MAX, &[Literal(0)], true, &[]);
        }
        let before = trace.entries().len();
        assert!(session.append(&[Literal(0)]).is_err());
        assert_eq!(
            session
                .solver
                .cold
                .clause_trace
                .as_ref()
                .unwrap()
                .entries()
                .len(),
            before
        );
        assert_eq!(session.solver.cold.original_ledger.clause_ids(), &[1]);
    }
}
