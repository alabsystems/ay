// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::checker::test_helpers::lit;
use crate::checker::{ConcludeResult, Stats};

fn healthy(work: usize, bytes: usize) -> Result<(), &'static str> {
    let _ = (work, bytes);
    Ok(())
}

#[test]
fn admitted_bootstrap_matches_ordinary_drup_defaults() {
    let mut reservations = Reservations::default();
    let checker = construct(3, &mut healthy, &mut reservations).unwrap();
    let ordinary = DratChecker::new(3, false);
    assert_eq!(reservations.attempts, 7);
    assert_eq!(checker.assigns, ordinary.assigns);
    assert_eq!(checker.reasons, ordinary.reasons);
    assert_eq!(checker.marks, ordinary.marks);
    assert_eq!(checker.conflict_marked, ordinary.conflict_marked);
    assert_eq!(checker.watches.len(), ordinary.watches.len());
    assert_eq!(checker.occ_lists, ordinary.occ_lists);
    assert_eq!(checker.hash_buckets, ordinary.hash_buckets);
    assert_eq!(checker.num_vars, 3);
    assert_eq!(checker.stats(), &Stats::default());
    assert!(!checker.check_rat);
    assert!(!checker.authority_tainted);
    assert!(checker.dense_refusal.is_none());
    assert_eq!(checker.conclude_unsat(), ordinary.conclude_unsat());
}

#[test]
fn actual_reservation_failure_at_each_of_seven_stages_returns_no_checker() {
    for stage in 0..7 {
        let mut reservations = Reservations {
            before_failure: Some(stage),
            ..Reservations::default()
        };
        let result = construct(3, &mut healthy, &mut reservations);
        assert!(matches!(
            result,
            Err(CheckerConstructionError::Allocation(_))
        ));
        assert_eq!(reservations.attempts, stage + 1);
    }
    let mut all = Reservations {
        before_failure: Some(7),
        ..Reservations::default()
    };
    assert!(construct(3, &mut healthy, &mut all).is_ok());
    assert_eq!(all.attempts, 7);
}

#[test]
fn every_admission_including_final_poll_can_refuse_without_a_checker() {
    let mut offers = Vec::new();
    let checker = DratChecker::try_new_drup_with_admission(3, &mut |work, bytes| {
        offers.push((work, bytes));
        Ok::<_, usize>(())
    })
    .unwrap();
    drop(checker);
    assert_eq!(offers.last(), Some(&(0, 0)));
    assert_eq!(offers.iter().filter(|(_, bytes)| *bytes != 0).count(), 7);
    for stop_at in 0..offers.len() {
        let mut calls = 0;
        let result = DratChecker::try_new_drup_with_admission(3, &mut |_, _| {
            let index = calls;
            calls += 1;
            if index == stop_at {
                Err(stop_at)
            } else {
                Ok(())
            }
        });
        assert!(matches!(result, Err(CheckerConstructionError::Admission(n)) if n == stop_at));
        assert_eq!(calls, stop_at + 1, "no callback after observed refusal");
    }
}

#[test]
fn interruption_during_first_array_fill_precedes_the_next_reservation() {
    let mut chunks = 0;
    let mut reservations = Reservations::default();
    let result = construct(
        4096,
        &mut |work, bytes| {
            if work > 1 && bytes == 0 {
                chunks += 1;
                assert!(work <= 2049);
                if chunks == 2 {
                    return Err("one-shot fill stop");
                }
            }
            Ok(())
        },
        &mut reservations,
    );
    assert!(matches!(
        result,
        Err(CheckerConstructionError::Admission("one-shot fill stop"))
    ));
    assert_eq!(chunks, 2);
    assert_eq!(reservations.attempts, 1);
}

#[test]
fn zero_variable_universe_still_admits_initial_hash_storage_and_fill() {
    let mut offers = Vec::new();
    let checker = DratChecker::try_new_drup_with_admission(0, &mut |work, bytes| {
        offers.push((work, bytes));
        Ok::<_, ()>(())
    })
    .unwrap();
    assert_eq!(checker.hash_buckets.len(), INITIAL_HASH_CAPACITY);
    assert!(checker.assigns.is_empty());
    assert_eq!(
        offers.iter().map(|(_, bytes)| bytes).sum::<usize>(),
        INITIAL_HASH_CAPACITY * size_of::<Vec<usize>>()
    );
    assert!(offers.iter().map(|(work, _)| work).sum::<usize>() > INITIAL_HASH_CAPACITY);
    let result = DratChecker::try_new_drup_with_admission(0, &mut |_, bytes| {
        if bytes > 0 {
            Err("hash storage")
        } else {
            Ok(())
        }
    });
    assert!(matches!(
        result,
        Err(CheckerConstructionError::Admission("hash storage"))
    ));
}

#[test]
fn impossible_universe_and_element_sizes_fail_before_reservation() {
    for num_vars in [MAX_DENSE_VARS + 1, usize::MAX] {
        let mut reservations = Reservations::default();
        let result = construct(num_vars, &mut healthy, &mut reservations);
        assert!(matches!(
            result,
            Err(CheckerConstructionError::VariableLimit { .. })
        ));
        assert_eq!(reservations.attempts, 0);
    }
    let mut reservations = Reservations::default();
    assert!(matches!(
        reservations.filled(0_u64, usize::MAX, &mut healthy),
        Err(CheckerConstructionError::SizeOverflow)
    ));
    assert_eq!(reservations.attempts, 0);
}

#[test]
fn admitted_drup_checker_keeps_authoritative_freshness_and_contradiction() {
    let mut checker = DratChecker::try_new_drup_with_admission(1, &mut healthy).unwrap();
    assert_ne!(checker.conclude_unsat(), ConcludeResult::Verified);
    assert!(checker.begin_bulk_verify().is_ok());
    assert!(checker.begin_bulk_verify().is_err());
    checker.add_original(&[lit(0, true)]);
    checker.add_original(&[lit(0, false)]);
    assert_eq!(checker.conclude_unsat(), ConcludeResult::Verified);
    assert!(!checker.authority_tainted);
}
