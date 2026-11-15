// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn a_transient_live_stop_cannot_reach_the_whole_set_probe() {
    use ay_core::time::Instant;
    use std::sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    };
    for reason in [
        crate::UnknownReason::Interrupted,
        crate::UnknownReason::Timeout,
    ] {
        let mut exec = loaded(FRAME);
        let flag = Arc::new(AtomicBool::new(false));
        exec.set_interrupt(flag.clone());
        let ten = int(&mut exec, 10);
        let mut plans = ReplayPlans::default();
        let instance = record_instance(&mut exec, &mut plans, 4, ten);
        let quantifier = exec.ctx.assertions[4];
        let selection = {
            let mut polls = 0;
            let mut stop = || {
                polls += 1;
                if polls != 3 {
                    return None;
                }
                if reason == crate::UnknownReason::Interrupted {
                    flag.store(true, Ordering::Relaxed);
                } else {
                    exec.solve_deadline.set(Some(Instant::now()));
                }
                let observed = exec.external_stop_reason();
                flag.store(false, Ordering::Relaxed);
                exec.solve_deadline.set(None);
                observed
            };
            let mut work = AnchorWork {
                remaining: MAX_ANCHOR_WORK,
                stop: &mut stop,
            };
            anchored_consequence_subset(
                &exec.ctx.terms,
                &[instance],
                &plans,
                &AndConjunctClosure::default(),
                &mut work,
            )
        };
        assert!(
            exec.external_stop_reason().is_none(),
            "live condition really recovered"
        );
        assert_eq!(selection, Err(AnchorFailure::Stopped(reason)));
        assert_eq!(exec.finish_anchor_selection(selection), Err(AnchorStopped));
        assert_eq!(exec.last_unknown_reason, Some(reason));
        let records = [crate::ematching::ForallInstantiationProvenance {
            quantifier,
            binding: vec![ten],
            instance,
        }];
        let attempts = exec.consequence_replay_attempts.get();
        assert!(exec
            .build_authored_consequence_replay_refutation(&records, &[], &[], &[], &[], &[])
            .is_none());
        assert_eq!(
            exec.consequence_replay_attempts.get(),
            attempts + 1,
            "the actual caller must reach anchored selection, not an earlier refusal"
        );
        assert_eq!(
            exec.consequence_replay_probe_claims(),
            0,
            "the actual caller must not take a whole-set fallback grant"
        );
        assert_eq!(exec.last_unknown_reason, Some(reason));
    }
}

#[test]
fn recorded_memory_and_deterministic_stops_forbid_any_probe_grant() {
    for origin in [
        crate::UnknownOrigin::MemoryBudget,
        crate::UnknownOrigin::DeterministicResourceBudget,
    ] {
        let mut exec = loaded(FRAME);
        let ten = int(&mut exec, 10);
        let mut plans = ReplayPlans::default();
        let instance = record_instance(&mut exec, &mut plans, 4, ten);
        let records = [crate::ematching::ForallInstantiationProvenance {
            quantifier: exec.ctx.assertions[4],
            binding: vec![ten],
            instance,
        }];
        exec.record_unknown_from_origin(origin);
        assert!(
            exec.external_stop_reason().is_none(),
            "no live flag or deadline required"
        );
        let attempts = exec.consequence_replay_attempts.get();
        assert!(exec
            .build_authored_consequence_replay_refutation(&records, &[], &[], &[], &[], &[])
            .is_none());
        assert_eq!(exec.consequence_replay_attempts.get(), attempts + 1);
        assert_eq!(exec.consequence_replay_probe_claims(), 0);
        assert_eq!(exec.last_unknown_reason, Some(origin.reason()));
    }
}
