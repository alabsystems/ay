// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Accounting of the consequence-replay probe envelope, in both currencies.

use super::*;
use std::time::Duration;

const SKOLEM: ProbeCap = ProbeCap::POSITIVE_SKOLEM;
const STANDARD: ProbeCap = ProbeCap::STANDARD;

#[test]
fn a_fresh_envelope_grants_the_whole_per_probe_cap() {
    let mut budget = ConsequenceReplayProbeBudget::default();
    let grant = budget.claim(SKOLEM, None).expect("fresh envelope grants");
    assert_eq!(grant.budget_ms(), 5_000);
    assert_eq!(grant.round_trips(), SKOLEM.round_trips);
    assert_eq!(budget.remaining_ms(), 0);
    assert_eq!(budget.remaining_round_trips(), 0);
}

/// The regression in one assertion: four probes that each burn their whole
/// slice cost the query ONE envelope, not four per-probe caps, in either
/// currency.
#[test]
fn four_exhausting_probes_cost_one_envelope_not_four_caps() {
    let mut budget = ConsequenceReplayProbeBudget::default();
    let (mut spent_ms, mut spent_round_trips) = (0, 0);
    for _ in 0..4 {
        let Some(grant) = budget.claim(SKOLEM, None) else {
            continue;
        };
        // A probe that exhausts its slice refunds nothing; a probe stopped by
        // its counted grant has started one round trip past it.
        budget.settle(grant, grant.budget_ms(), grant.round_trips() + 1);
        spent_ms += grant.budget_ms();
        spent_round_trips += grant.round_trips();
    }
    assert_eq!(
        spent_ms, QUERY_PROBE_BUDGET_MS,
        "the lane's total wall spend per query must be the envelope, not 4 x the per-probe cap"
    );
    assert_eq!(spent_round_trips, QUERY_PROBE_ROUND_TRIPS);
    assert_eq!(budget.granted_round_trips(), QUERY_PROBE_ROUND_TRIPS);
}

/// Standard probes draw on the same counted envelope: it, not the number of
/// probes, bounds their total.
#[test]
fn standard_probes_share_one_counted_envelope() {
    let mut budget = ConsequenceReplayProbeBudget::default();
    let mut spent_round_trips = 0;
    while let Some(grant) = budget.claim(STANDARD, None) {
        budget.settle(grant, 0, grant.round_trips());
        spent_round_trips += grant.round_trips();
    }
    assert!(spent_round_trips <= QUERY_PROBE_ROUND_TRIPS);
    assert!(QUERY_PROBE_ROUND_TRIPS - spent_round_trips < MIN_PROBE_ROUND_TRIPS);
    assert_eq!(
        budget.remaining_ms(),
        QUERY_PROBE_BUDGET_MS,
        "probes stopped by their count spent no wall time here"
    );
}

#[test]
fn an_unspent_grant_is_refunded_for_the_next_probe() {
    let mut budget = ConsequenceReplayProbeBudget::default();
    let first = budget.claim(SKOLEM, None).expect("fresh envelope grants");
    budget.settle(first, 40, 3);
    assert_eq!(budget.remaining_ms(), QUERY_PROBE_BUDGET_MS - 40);
    assert_eq!(budget.remaining_round_trips(), QUERY_PROBE_ROUND_TRIPS - 3);
    let second = budget
        .claim(SKOLEM, None)
        .expect("refunded envelope grants");
    assert_eq!(second.budget_ms(), QUERY_PROBE_BUDGET_MS - 40);
    assert_eq!(second.round_trips(), QUERY_PROBE_ROUND_TRIPS - 3);
}

#[test]
fn a_slice_below_the_floor_is_declined_rather_than_granted() {
    let mut budget = ConsequenceReplayProbeBudget::default();
    budget.set_remaining_ms(MIN_PROBE_BUDGET_MS - 1);
    assert!(budget.claim(SKOLEM, None).is_none());
    assert_eq!(
        budget.remaining_ms(),
        MIN_PROBE_BUDGET_MS - 1,
        "a declined claim must not deduct"
    );
    assert_eq!(budget.remaining_round_trips(), QUERY_PROBE_ROUND_TRIPS);
}

/// The counted floor declines exactly like the wall floor, and deducts
/// nothing in either currency.
#[test]
fn a_counted_slice_below_the_floor_is_declined_rather_than_granted() {
    let mut budget = ConsequenceReplayProbeBudget::default();
    budget.set_remaining_round_trips(MIN_PROBE_ROUND_TRIPS - 1);
    assert!(budget.claim(SKOLEM, None).is_none());
    assert_eq!(budget.remaining_round_trips(), MIN_PROBE_ROUND_TRIPS - 1);
    assert_eq!(budget.remaining_ms(), QUERY_PROBE_BUDGET_MS);
    assert_eq!(budget.claims(), 0);
    budget.set_remaining_round_trips(MIN_PROBE_ROUND_TRIPS);
    let grant = budget
        .claim(SKOLEM, None)
        .expect("the floor itself is granted");
    assert_eq!(grant.round_trips(), MIN_PROBE_ROUND_TRIPS);
}

#[test]
fn a_probe_may_not_claim_the_callers_whole_remaining_deadline() {
    let mut budget = ConsequenceReplayProbeBudget::default();
    let deadline = Instant::now() + Duration::from_secs(3);
    let grant = budget
        .claim(SKOLEM, Some(deadline))
        .expect("grants a share");
    assert!(
        grant.budget_ms() <= 1_500,
        "a probe claimed {}ms of a 3000ms remaining deadline",
        grant.budget_ms()
    );
    // The caller's deadline is the outer WALL: it shares out the backstop
    // only. The counted grant stays the cap's, so where the probe stops does
    // not depend on how much of the deadline happened to be left.
    assert_eq!(grant.round_trips(), SKOLEM.round_trips);
}

#[test]
fn an_expired_deadline_declines_instead_of_granting() {
    let mut budget = ConsequenceReplayProbeBudget::default();
    let deadline = Instant::now();
    assert!(budget.claim(SKOLEM, Some(deadline)).is_none());
}

#[test]
fn claims_count_grants_not_declines_and_rearm_at_the_boundary() {
    let mut budget = ConsequenceReplayProbeBudget::default();
    let grant = budget.claim(STANDARD, None).expect("fresh envelope grants");
    budget.settle(grant, 10, 1);
    assert_eq!(budget.claims(), 1);
    budget.set_remaining_ms(MIN_PROBE_BUDGET_MS - 1);
    assert!(budget.claim(STANDARD, None).is_none());
    assert_eq!(budget.claims(), 1, "a declined claim must not count");
    budget.begin_external_query();
    assert_eq!(budget.claims(), 0);
}

#[test]
fn the_external_query_boundary_replenishes() {
    let mut budget = ConsequenceReplayProbeBudget::default();
    let grant = budget.claim(SKOLEM, None).expect("fresh envelope grants");
    budget.settle(grant, grant.budget_ms(), grant.round_trips());
    assert_eq!(budget.remaining_ms(), 0);
    assert_eq!(budget.remaining_round_trips(), 0);
    budget.begin_external_query();
    assert_eq!(budget.remaining_ms(), QUERY_PROBE_BUDGET_MS);
    assert_eq!(budget.remaining_round_trips(), QUERY_PROBE_ROUND_TRIPS);
    assert_eq!(budget.granted_round_trips(), 0);
}

/// The calibration documented at [`ProbeCap`], as bounds.
///
/// Capability: every proving probe measured fits its count with headroom (at
/// most 7 round trips under a standard plan, 4 in its anchored attempt, 1
/// under a positive-Skolem plan and 50 in its anchored attempt), and so does
/// every scoped whole-set probe whose unpromotable raw UNSAT arms the unscoped
/// retry (at most 59, under a standard plan; at most 1 under a positive-Skolem
/// plan). Wall: the costliest rounds measured (14.1 ms on an A725 core) fit
/// every count inside its own wall cap, so the count, not the wall, is what
/// stops such a probe.
#[test]
fn the_calibration_admits_every_measured_proof_and_fits_the_slow_core_wall() {
    const ANCHORED: u64 = 4;
    assert_eq!(STANDARD.wall_ms, 2_000, "the wall caps are unchanged");
    assert_eq!(SKOLEM.wall_ms, QUERY_PROBE_BUDGET_MS);
    // A scoped whole-set probe's unpromotable raw UNSAT arms the unscoped
    // retry: the most such a probe used is 59 round trips.
    assert!(STANDARD.round_trips > 59 && STANDARD.share(ANCHORED).round_trips >= 4);
    assert!(SKOLEM.round_trips >= 1 && SKOLEM.share(ANCHORED).round_trips >= 50);
    let slowest_round_us = 14_100;
    for cap in [
        STANDARD,
        SKOLEM,
        STANDARD.share(ANCHORED),
        SKOLEM.share(ANCHORED),
    ] {
        assert!(
            cap.round_trips * slowest_round_us <= cap.wall_ms * 1_000,
            "{cap:?}: the count must stop the costliest measured rounds inside the wall"
        );
    }
    assert!(
        MIN_PROBE_ROUND_TRIPS > 0 && MIN_PROBE_ROUND_TRIPS <= STANDARD.share(ANCHORED).round_trips
    );
}
