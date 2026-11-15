// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn borrowed_progress_is_consulted_inside_original_clause_replay() {
    let (problem, derivation) = evidence(32);
    let mut original = Owner::capture().expect("original owner");
    let mut offers = 0usize;
    let result = {
        let mut progress = || {
            offers += 1;
            offers < 80
        };
        validate(
            &problem,
            &derivation,
            &mut original.with_progress(&mut progress),
        )
    };
    assert_eq!(result, Err(Error::Stopped));
    assert_eq!(offers, 80);
    assert_eq!(original.poll(), Err(Error::Stopped));
    let mut healthy = || true;
    assert_eq!(
        original.with_progress(&mut healthy).poll(),
        Err(Error::Stopped)
    );
}

#[test]
fn borrowed_callback_unwind_latches_original_even_after_catch() {
    let mut original = Owner::capture().expect("original owner");
    let mut progress = || -> bool { panic!("borrowed observer unwind") };
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        original.with_progress(&mut progress).poll()
    }))
    .is_err());
    assert_eq!(original.poll(), Err(Error::Stopped));
}

#[test]
fn carried_evidence_is_send_sync_and_reuses_observed_refusal() {
    fn send_sync<T: Send + Sync>() {}
    send_sync::<CompactEvidence>();
    let (problem, derivation) = evidence(10);
    let original = Owner::capture().expect("owner");
    let carried = CompactEvidence::new(derivation, original);
    assert_eq!(carried.validate(&problem), Ok(()));
    let mut offer = carried.owner();
    assert_eq!(offer.refuse::<()>(Error::Resource), Err(Error::Resource));
    assert_eq!(carried.validate(&problem), Err(Error::Resource));
}
