// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Barrier for the consequence-replay lane's per-query WALL envelope.
//!
//! # What broke, and why the existing tests did not name it
//!
//! `9e5793ba81` ("certify finite frame consequence proofs") raised
//! `PROBE_BUDGET_MS` from 2 s to 5 s so the u64 frame obligation could finish
//! its ground probe — a real, wanted capability. Nothing capped how many probes
//! one public `check-sat` could run: `MAX_REPLAY_ATTEMPTS` is per
//! consequence-replay SCOPE and `take_consequence_replay_state` hands every
//! nested scope a fresh pair. On `sum_datatype_forall` the raise multiplied out
//! to 4 x 5 s = 20 s of probes that decline 4-for-4, on a query whose actual
//! refutation costs ~50 ms, and six demand-lane tests went `unsat -> unknown`
//! against their 15 s / 20 s caps. No certificate refused anything: the engine
//! derived the refutation and could have published it, but the lane had spent
//! the clock.
//!
//! `demand_probes` and `demand_lane_shadow` catch the SYMPTOM (`unknown`). They
//! do not distinguish the two ways to make it go away, and one of them is a
//! regression of its own: lowering `PROBE_BUDGET_MS` back to 2 s turns all six
//! green again while removing the capability the commit added. This module pins
//! the MECHANISM instead — a bound on what the lane may claim per query — so
//! that path is not open.
//!
//! # Why the assertion is an accounting read, not a stopwatch
//!
//! Wall time on a loaded host is not a measurement. `granted_ms` is decided
//! entirely by `ConsequenceReplayProbeBudget::claim`, so the bound below holds
//! (or fails) identically at load 0 and load 60.

use std::time::Duration;

use super::demand_probes::GREEN_SUM_DATATYPE_FORALL;
use crate::Executor;
use ay_frontend::parse;

/// The nominal cap `demand_probes::GREEN_TIMEOUT` applies to this same input.
const QUERY_TIMEOUT: Duration = Duration::from_secs(15);

/// The whole regression as one bound: however many consequence-replay scopes a
/// single public query opens, the lane may claim at most ONE envelope of probe
/// wall clock in total.
///
/// The lower bound is the anti-vacuity clause. Without it this test passes
/// trivially on any build where the lane never runs — including a build that
/// disabled it outright — which is precisely the shape of barrier this repo has
/// shipped three times and had pass under the mutation it was written for.
#[test]
fn one_public_query_grants_at_most_one_probe_envelope() {
    let commands = parse(GREEN_SUM_DATATYPE_FORALL).expect("parse the sum-datatype green probe");
    let mut exec = Executor::new();
    exec.set_timeout(Some(QUERY_TIMEOUT));
    let outputs = exec
        .execute_all(&commands)
        .expect("the sum-datatype green probe must execute");

    let granted = exec.consequence_replay_probe_ms_granted();
    let envelope = Executor::consequence_replay_probe_envelope_ms();

    assert!(
        granted > 0,
        "ANTI-VACUITY: the consequence-replay lane granted no probe budget at all \
         on this input, so the bound below proves nothing. Either the lane stopped \
         running here (in which case this barrier no longer covers the regression \
         and must be re-pointed at an input that does reach the probe) or the \
         accounting is not wired up."
    );
    assert!(
        granted <= envelope,
        "the consequence-replay lane claimed {granted}ms of probe wall clock in one \
         public query, over the {envelope}ms envelope. That budget is spent out of \
         the caller's publication window: this is the exact shape that turned six \
         already-derived refutations into `unknown` under 9e5793ba81."
    );
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("unsat"),
        "the refutation is derived in ~50ms and must still be PUBLISHED within \
         {QUERY_TIMEOUT:?}; `unknown` here means the lane spent the window again"
    );
}
