// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Live-byte settlement on drop and per-obligation work envelopes.

use super::super::super::{
    check_plain_unsat_retained_native_with_progress, BoundRetainedProofBytes,
};
use super::*;

const UNSAT: &str = "(declare-const x Int) (assert (> x 5)) (assert (< x 3)) (check-sat)";
const ROWS: usize = 8;

fn request(callback: &mut dyn FnMut() -> bool) -> RetainedReplayProgress<'_> {
    RetainedReplayProgress::new_for_retained_rows(ReplayLimit::Until(deadline()), callback, ROWS)
        .unwrap()
}

/// One complete obligation: live discharge, encoding, admission, cleanup.
fn obligation(owner: &mut RetainedReplayProgress<'_>) -> Result<(), String> {
    let proof = check_plain_unsat_retained_native_with_progress(UNSAT, owner)?;
    let bytes = proof.encode(owner)?;
    bytes.admit(owner)?;
    drop(bytes);
    owner.check()
}

/// `count` obligations, each declared first when `declared`; the first error.
fn run(owner: &mut RetainedReplayProgress<'_>, declared: bool, count: usize) -> Result<(), usize> {
    for index in 0..count {
        if declared {
            owner.begin_obligation().map_err(|_| index)?;
        }
        obligation(owner).map_err(|_| index)?;
    }
    Ok(())
}

fn survivors(bytes: &BoundRetainedProofBytes) -> usize {
    bytes.query.capacity() + bytes.bundle.capacity()
}

/// Work and bytes one obligation debits on a request that declares none.
fn bare_obligation() -> (usize, usize) {
    let mut callback = || true;
    let mut bare = request(&mut callback);
    let base = (bare.work, bare.bytes);
    obligation(&mut bare).unwrap();
    (bare.work - base.0, bare.bytes - base.1)
}

#[test]
fn a_dropped_settlement_returns_exactly_its_bytes_and_never_its_work() {
    let mut callback = || true;
    let mut owner = request(&mut callback);
    owner.begin_obligation().unwrap();
    let base = (owner.work, owner.bytes);
    let settlement = owner.settlement().unwrap();
    assert!(settlement.settles());
    assert!(owner.charge(5, 1000));
    assert!(owner.check().is_ok());
    assert_eq!(owner.bytes, base.1 + 1000, "a live token returns nothing");
    drop(settlement);
    assert_eq!(owner.bytes, base.1 + 1000, "returned at the next admission");
    assert!(owner.check().is_ok());
    assert_eq!((owner.work, owner.bytes), (base.0 + 5, base.1));
}

#[test]
fn a_live_proof_owner_keeps_its_bytes_until_it_drops() {
    let mut callback = || true;
    let mut owner = request(&mut callback);
    owner.begin_obligation().unwrap();
    let base = owner.bytes;
    let proof = check_plain_unsat_retained_native_with_progress(UNSAT, &mut owner).unwrap();
    let live = owner.bytes;
    assert!(live > base);
    assert!(owner.check().is_ok());
    assert_eq!(
        owner.bytes, live,
        "polls under a live proof owner return nothing"
    );
    drop(proof);
    assert!(owner.check().is_ok());
    assert_eq!(
        owner.bytes, base,
        "the dropped proof returns every byte it debited"
    );

    owner.begin_obligation().unwrap();
    let proof = check_plain_unsat_retained_native_with_progress(UNSAT, &mut owner).unwrap();
    let bytes = proof.encode(&mut owner).unwrap();
    assert!(owner.check().is_ok());
    assert_eq!(
        owner.bytes,
        base + survivors(&bytes),
        "only the encoded survivors stay debited"
    );
}

#[test]
fn five_settled_obligations_fit_one_peak_and_oversized_or_unsettled_runs_are_refused() {
    let (_, peak) = bare_obligation();
    let survivors = {
        let mut callback = || true;
        let mut probe = request(&mut callback);
        probe.begin_obligation().unwrap();
        let base = probe.bytes;
        obligation(&mut probe).unwrap();
        probe.bytes - base
    };
    // Survivors of four settled obligations plus one obligation's peak.
    let need = 4 * survivors + peak;
    assert!(
        survivors > 0 && 5 * peak > need,
        "must not fit cumulatively"
    );
    for (declared, ceiling, count, failing) in [
        (true, need, 5, None),
        (true, need - 1, 5, Some(4)),
        (true, peak - 1, 1, Some(0)),
        (false, need, 5, Some(1)),
    ] {
        let mut callback = || true;
        let mut owner = request(&mut callback);
        owner.max_bytes = owner.bytes + ceiling;
        let result = run(&mut owner, declared, count);
        assert_eq!(result.err(), failing, "{declared} {ceiling} {count}");
        // A ledger debit or a phase's own preflight against the remaining
        // allowance may refuse first; either way the owner stays stopped.
        assert_eq!(owner.check().is_ok(), failing.is_none());
    }
}

#[test]
fn each_obligation_gets_one_work_envelope_and_at_most_obligations_times_it() {
    let (work, _) = bare_obligation();
    // (declared, envelope, initial cumulative allowance, first failing row)
    for (declared, envelope, allowance, failing) in [
        (true, work, work, None),
        (true, work, 5 * work, None),
        (true, work - 1, 5 * work, Some(0)),
        (false, work, work, Some(1)),
    ] {
        let mut callback = || true;
        let mut owner = request(&mut callback);
        let start = owner.work;
        owner.obligations.envelope = envelope;
        owner.max_work = start + allowance;
        let result = run(&mut owner, declared, 5);
        // With an ample cumulative allowance only the envelope can refuse;
        // encoding's own preflight against the narrowed limits may be first.
        assert_eq!(result.err(), failing, "{declared} {envelope} {allowance}");
        match failing {
            None => assert_eq!(owner.work, start + 5 * work),
            Some(_) => assert!(owner.check().is_err()),
        }
        if !declared {
            assert_eq!(owner.first_refusal, Some(Refusal::WorkCeiling));
        } else if allowance == work {
            assert_eq!(
                owner.max_work,
                start + 5 * work,
                "one envelope per obligation"
            );
        }
    }
}

#[test]
fn ceilings_stay_one_row_for_any_row_count_and_rows_bound_the_obligations() {
    for rows in [1, 6, 42] {
        let mut callback = || true;
        let mut owner = RetainedReplayProgress::new_for_retained_rows(
            ReplayLimit::Until(deadline()),
            &mut callback,
            rows,
        )
        .unwrap();
        // One row's three metered walks of work; bytes stay one proof's.
        assert_eq!(
            owner.max_work as u64,
            3 * MAX_PROOF_PRODUCING_BV_LEMMAS_PER_PROOF as u64
                * MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA
        );
        assert!(
            owner.max_bytes
                <= MAX_PROOF_PRODUCING_BV_LEMMAS_PER_PROOF * MAX_PROOF_PRODUCING_BV_BYTES_PER_LEMMA
        );
        let envelope = owner.max_work;
        assert_eq!(owner.obligations.envelope, envelope);
        for _ in 0..rows {
            owner.begin_obligation().unwrap();
        }
        assert_eq!(
            owner.max_work,
            rows * envelope,
            "at most rows x one envelope"
        );
        assert_eq!(
            owner.begin_obligation(),
            Err(Refusal::ObligationCount.message().to_string())
        );
        assert!(owner.check().is_err());
    }
}

#[test]
fn bare_settlements_are_inert_and_misuse_fails_closed() {
    let mut callback = || true;
    let mut bare = request(&mut callback);
    let settlement = bare.settlement().unwrap();
    assert!(!settlement.settles());
    assert!(bare.charge(0, 100));
    let kept = bare.bytes;
    drop(settlement);
    assert!(bare.check().is_ok());
    assert_eq!(
        bare.bytes, kept,
        "a request without obligations stays cumulative"
    );

    let mut callback = || true;
    let mut live = request(&mut callback);
    live.begin_obligation().unwrap();
    let proof = check_plain_unsat_retained_native_with_progress(UNSAT, &mut live).unwrap();
    assert!(live.begin_obligation().is_err());
    drop(proof);
    assert!(
        live.check().is_err(),
        "a refused obligation is never revived"
    );

    let mut callback = || true;
    let mut nested = request(&mut callback);
    nested.begin_obligation().unwrap();
    let outer = nested.settlement().unwrap();
    assert!(nested.settlement().is_err());
    drop(outer);
    assert!(nested.check().is_err());

    let mut callback = || true;
    let mut corrupt = request(&mut callback);
    corrupt.begin_obligation().unwrap();
    let settlement = corrupt.settlement().unwrap();
    assert!(corrupt.charge(0, 10));
    corrupt.bytes = 5;
    drop(settlement);
    assert_eq!(
        corrupt.check(),
        Err(Refusal::SettlementUnderflow.message().to_string())
    );
}
