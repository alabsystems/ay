// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// First refusal never extends the caller's budget, and never fires when
/// there is no budget worth granting.
#[test]
fn first_refusal_is_bounded_by_the_caller_and_by_the_model_cap() {
    use std::time::{Duration, Instant};
    let now = Instant::now();
    let cap = ANCHOR_FIRST_REFUSAL_CAP;

    // No caller deadline: the model-derived cap binds.
    let plan =
        AnchorFirstRefusal::plan_with_cap(now, None, cap).expect("unlimited solve gets a slice");
    assert_eq!(plan.until, now + cap);

    // A tighter caller deadline binds instead. NEVER extended.
    let tight = now + Duration::from_millis(300);
    let plan =
        AnchorFirstRefusal::plan_with_cap(now, Some(tight), cap).expect("300ms is worth granting");
    assert_eq!(plan.until, tight);

    // A generous caller deadline does NOT buy a longer slice: speculation
    // costs O(model), not O(deadline). This is the property whose absence
    // made markshare_5_0 slower the more time it was given.
    let generous = now + Duration::from_mins(10);
    let plan = AnchorFirstRefusal::plan_with_cap(now, Some(generous), cap).expect("plenty of time");
    assert_eq!(plan.until, now + cap);

    // Already expired, or too small to be worth anything: no deferral.
    assert!(AnchorFirstRefusal::plan_with_cap(now, Some(now), cap).is_none());
    assert!(
        AnchorFirstRefusal::plan_with_cap(now, Some(now + Duration::from_millis(1)), cap).is_none()
    );
}

#[test]
fn unrepresentable_refusal_cap_without_caller_deadline_disables_deferral() {
    use std::time::{Duration, Instant};
    let now = Instant::now();
    assert!(now.checked_add(Duration::MAX).is_none());
    assert!(AnchorFirstRefusal::plan_with_cap(now, None, Duration::MAX).is_none());
}

#[test]
fn caller_deadline_bounds_an_unrepresentable_refusal_cap() {
    use std::time::{Duration, Instant};
    let now = Instant::now();
    assert!(now.checked_add(Duration::MAX).is_none());
    let deadline = now + Duration::from_mins(1);
    let plan = AnchorFirstRefusal::plan_with_cap(now, Some(deadline), Duration::MAX)
        .expect("explicit deadline supplies a finite refusal window");
    assert_eq!(plan.until, deadline);
}

/// THE DEGENERATE POINT. `--anchor-first-refusal-ms` switches
/// deferral off, which is what makes the dominance invariant checkable as a
/// property of ONE program with a parameter rather than as a claim about
/// two programs.
#[test]
fn a_zero_cap_disables_deferral_entirely() {
    use std::time::{Duration, Instant};
    let now = Instant::now();
    assert!(AnchorFirstRefusal::plan_with_cap(
        now,
        Some(now + Duration::from_mins(10)),
        Duration::ZERO
    )
    .is_none());
    assert!(AnchorFirstRefusal::plan_with_cap(now, None, Duration::ZERO).is_none());
}

/// `LaneFrame` must not let a declining lane's replay claim attach to
/// somebody else's verdict, and must not eat the caller's own pending
/// claims either.
#[test]
fn lane_frame_isolates_a_lanes_ledger_from_the_callers() {
    fn claim(name: &str) -> crate::cert_io::ReplayClaim {
        crate::cert_io::ReplayClaim {
            claim: name.to_owned(),
            device: "t".to_owned(),
            method: "t".to_owned(),
            arithmetic: "exact".to_owned(),
            nodes_visited: None,
            node_budget: 0,
            outcome: "exhausted".to_owned(),
            nondeterminism: Vec::new(),
            reproduce: "t".to_owned(),
            tcb: "t".to_owned(),
        }
    }
    let _drain = crate::cert_io::ledger::take();

    crate::cert_io::ledger::record(claim("caller"));
    {
        let frame = LaneFrame::enter();
        crate::cert_io::ledger::record(claim("lane"));
        let mine = frame.take_lane_claims();
        assert_eq!(mine.len(), 1);
        assert_eq!(mine[0].claim, "lane");
    }
    let after = crate::cert_io::ledger::take();
    assert_eq!(after.len(), 1, "the caller's claim must survive the frame");
    assert_eq!(after[0].claim, "caller");

    // And a lane that DECLINES (frame dropped without harvest) must leave
    // nothing behind for the next verdict to inherit.
    crate::cert_io::ledger::record(claim("caller"));
    {
        let _frame = LaneFrame::enter();
        crate::cert_io::ledger::record(claim("declined-lane"));
    }
    let after = crate::cert_io::ledger::take();
    assert_eq!(
        after.len(),
        1,
        "a declining lane's claim must not survive its frame"
    );
    assert_eq!(after[0].claim, "caller");
}
