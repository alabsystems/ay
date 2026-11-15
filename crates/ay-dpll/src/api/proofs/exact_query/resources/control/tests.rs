// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::cell::Cell;
use std::panic::{catch_unwind, AssertUnwindSafe};

fn source() -> [TermId; 5] {
    [TermId(7), TermId(2), TermId(7), TermId(9), TermId(2)]
}

fn operations(control: &mut Control<'_>) -> Result<Vec<TermId>, ProofCheckError> {
    let copied = control.copy_ids(&source())?;
    let unique = control.ordered_unique_ids(&copied)?;
    assert!(control.all_ids_in(&copied, &unique)?);
    assert!(!control.all_ids_in(&[TermId(11)], &unique)?);
    Ok(unique)
}

fn trace() -> Vec<(usize, usize)> {
    let mut charges = Vec::new();
    assert_eq!(
        Control::new(&mut |work, bytes| {
            charges.push((work, bytes));
            true
        })
        .run(operations)
        .unwrap(),
        [TermId(7), TermId(2), TermId(9)]
    );
    charges
}

fn totals(charges: &[(usize, usize)]) -> (usize, usize) {
    charges
        .iter()
        .fold((0usize, 0usize), |(work, bytes), (w, b)| {
            (
                work.checked_add(*w).unwrap(),
                bytes.checked_add(*b).unwrap(),
            )
        })
}

#[test]
fn copies_and_membership_preserve_exact_ids_and_first_use_order() {
    let mut progress = |_, _| true;
    let mut control = Control::new(&mut progress);
    assert_eq!(control.copy_ids(&source()).unwrap(), source());
    assert_eq!(
        operations(&mut control).unwrap(),
        [TermId(7), TermId(2), TermId(9)]
    );
    assert_eq!(control.copy_ids(&[]).unwrap(), []);
    assert_eq!(control.ordered_unique_ids(&[]).unwrap(), []);
    assert!(control.all_ids_in(&[], &[]).unwrap());
    assert!(!control.all_ids_in(&[TermId(0)], &[]).unwrap());
    // No liveness or proof interpretation is introduced by these data helpers.
    assert_eq!(
        control.ordered_unique_ids(&[TermId::SENTINEL; 3]).unwrap(),
        [TermId::SENTINEL]
    );
}

#[test]
fn exact_and_one_short_allowances_cover_all_copy_and_comparison_work() {
    let (work, bytes) = totals(&trace());
    assert_eq!(bytes, 2 * source().len() * size_of::<TermId>());
    for (work_cap, bytes_cap, admitted) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
        (0, bytes, false),
        (work, 0, false),
    ] {
        let (mut w, mut b) = (0, 0);
        let result = Control::new(&mut |dw, db| {
            w += dw;
            b += db;
            w <= work_cap && b <= bytes_cap
        })
        .run(operations);
        assert_eq!(result.is_ok(), admitted);
        if !admitted {
            assert_eq!(result, Err(ProofCheckError::ResourceLimit));
        }
    }
}

#[test]
fn every_checkpoint_is_terminal_even_if_the_callback_would_resume() {
    let expected = trace();
    for stop in 1..=expected.len() {
        let mut actual = Vec::new();
        {
            let mut progress = |w, b| {
                actual.push((w, b));
                actual.len() != stop
            };
            let mut control = Control::new(&mut progress);
            assert_eq!(control.run(operations), Err(ProofCheckError::ResourceLimit));
            assert_eq!(control.charge(0, 0), Err(ProofCheckError::ResourceLimit));
            assert_eq!(control.copy_ids(&[]), Err(ProofCheckError::ResourceLimit));
            assert_eq!(
                control.ordered_unique_ids(&[]),
                Err(ProofCheckError::ResourceLimit)
            );
            assert_eq!(
                control.all_ids_in(&[], &[]),
                Err(ProofCheckError::ResourceLimit)
            );
        }
        assert_eq!(actual, expected[..stop]);
    }
    assert_eq!(trace(), expected);
}

#[test]
fn quadratic_membership_and_dedup_comparisons_are_individually_prepaid() {
    let ids: Vec<_> = (0..12).map(TermId).collect();
    let mut charges = Vec::new();
    let unique = Control::new(&mut |w, b| {
        charges.push((w, b));
        true
    })
    .ordered_unique_ids(&ids)
    .unwrap();
    assert_eq!(unique, ids);
    let comparisons = ids.len() * (ids.len() - 1) / 2;
    assert_eq!(
        totals(&charges),
        (
            1 + 2 * ids.len() + comparisons,
            ids.len() * size_of::<TermId>()
        )
    );
    let mut work = 0;
    assert!(Control::new(&mut |w, b| {
        assert_eq!(b, 0);
        work += w;
        true
    })
    .all_ids_in(&[ids[11]; 3], &ids)
    .unwrap());
    assert_eq!(work, 3 * (1 + ids.len()));
}

#[test]
fn same_callback_keeps_prior_consumption_across_fresh_controls() {
    let (work, bytes) = totals(&trace());
    let (mut w, mut b) = (0, 0);
    let mut progress = |dw, db| {
        w += dw;
        b += db;
        w <= work && b <= bytes
    };
    assert!(Control::new(&mut progress).run(operations).is_ok());
    assert_eq!(
        Control::new(&mut progress).run(operations),
        Err(ProofCheckError::ResourceLimit)
    );
    assert_eq!(totals(&trace()), (work, bytes));
}

#[test]
fn caught_callback_panic_cannot_resume_the_operation_or_control() {
    let calls = Cell::new(0);
    let mut progress = |_, _| {
        calls.set(calls.get() + 1);
        if calls.get() == 2 {
            panic!("expected resource callback panic");
        }
        true
    };
    let mut control = Control::new(&mut progress);
    let result = control.run(|control| {
        assert!(catch_unwind(AssertUnwindSafe(|| control.charge(1, 1))).is_err());
        assert_eq!(control.charge(0, 0), Err(ProofCheckError::ResourceLimit));
        Ok(17)
    });
    assert_eq!(result, Err(ProofCheckError::ResourceLimit));
    assert_eq!(control.charge(0, 0), Err(ProofCheckError::ResourceLimit));
    assert_eq!(calls.get(), 2);
}

#[test]
fn arithmetic_and_downstream_resource_refusals_latch_without_later_callbacks() {
    let calls = Cell::new(0);
    let mut progress = |_, _| {
        calls.set(calls.get() + 1);
        true
    };
    let mut control = Control::new(&mut progress);
    assert_eq!(
        control.reserve_ids(usize::MAX),
        Err(ProofCheckError::ResourceLimit)
    );
    assert_eq!(calls.get(), 1);
    assert_eq!(control.charge(0, 0), Err(ProofCheckError::ResourceLimit));
    let mut reserve = Control::new(&mut progress);
    // Product fits usize, but Vec's isize-sized allocation layout must refuse
    // before attempting a giant allocation.
    let too_many = (isize::MAX as usize / size_of::<TermId>()) + 1;
    assert_eq!(
        reserve.reserve_ids(too_many),
        Err(ProofCheckError::ResourceLimit)
    );
    assert_eq!(calls.get(), 3);
    assert_eq!(reserve.charge(0, 0), Err(ProofCheckError::ResourceLimit));
    let mut fresh = Control::new(&mut progress);
    assert_eq!(
        fresh.run::<()>(|_| Err(ProofCheckError::ResourceLimit)),
        Err(ProofCheckError::ResourceLimit)
    );
    assert_eq!(calls.get(), 4);
    assert_eq!(fresh.charge(0, 0), Err(ProofCheckError::ResourceLimit));
    assert_eq!(calls.get(), 4);
}

/// #completed-check-accepted: once the export has returned, the caller is not
/// consulted again, so a stop it would raise now (here: once the export's
/// temporaries are gone) cannot discard the completed result.
#[test]
fn no_poll_follows_a_completed_export() {
    struct Dropped<'a>(&'a Cell<bool>);
    impl Drop for Dropped<'_> {
        fn drop(&mut self) {
            self.0.set(true);
        }
    }
    let dropped = Cell::new(false);
    let mut calls = 0;
    let mut progress = |w, b| {
        calls += 1;
        assert_eq!((w, b), (0, 0));
        !dropped.get()
    };
    assert_eq!(
        Control::new(&mut progress).run(|_| {
            let _temporary = Dropped(&dropped);
            Ok(17)
        }),
        Ok(17)
    );
    assert!(dropped.get());
    assert_eq!(
        calls, 1,
        "only the admission poll; nothing after completion"
    );
}

mod retained;
