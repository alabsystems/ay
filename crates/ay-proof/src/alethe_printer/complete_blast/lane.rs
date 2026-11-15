// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The lane that printed each planned lemma, so a later render of the same
//! plan goes straight to it.
//!
//! `Blaster::finish_planned` tries a large circuit's lanes in order — the
//! direct refutation, the case split, the sweep — and the first that prints
//! wins. One publication renders a lemma several times (the support
//! question, the strict document scan, the export), and a lane that declined
//! at the first render declines again at every later one: its limits are
//! conflict counts over the same CNF, and a decline is never memoized by the
//! refutation memo. Measured 2026-10-01 on proof_gate_strict row 1257,
//! whose document is the case split's: every render after the first spent
//! 2.3 to 2.5 s (load average ~100 on 18 cores) in a direct attempt that had
//! already declined, before the case split's retained refutation printed in
//! 0.8 s. The sweep's own retention already skipped the lanes before it
//! (`transport.rs`), but only while the refutation memo kept the sweep: a
//! publication with two large lemmas evicts it.
//!
//! A plan is known by its gate count, its clause count and a fingerprint of
//! its clauses: the full CNF is the refutation memo's key, and keeping it a
//! second time here would double the retained memory for nothing a
//! fingerprint does not give. The record decides only which lanes are
//! TRIED: a lane skipped this way had declined, every document is replayed
//! before it is printed, and the sweep and the monolithic refutation still
//! follow a remembered lane that does not print. A colliding fingerprint can
//! therefore cost a document, never admit one.

use ay_core::kani_compat::DetHashMap;
use ay_sat::Literal;
use std::cell::RefCell;
use std::hash::{Hash, Hasher};

/// A lane that prints a large circuit's document after another declined.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Lane {
    /// The case split (`crate::sat_sweep::split`): the direct lane declined.
    Cases,
    /// The sweep: the direct lane and the case split declined.
    Sweep,
}

/// A planned CNF, as this record knows it.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(super) struct Plan {
    variables: usize,
    clauses: usize,
    fingerprint: u64,
}

impl Plan {
    /// The plan of `cnf` over `variables` gates.
    pub(super) fn of(variables: usize, cnf: &[Vec<Literal>]) -> Self {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        cnf.hash(&mut hasher);
        Self {
            variables,
            clauses: cnf.len(),
            fingerprint: hasher.finish(),
        }
    }
}

/// Plans remembered before the record is dropped wholesale.
const MAX_PLANS: usize = 4_096;

thread_local! {
    static PRINTED_BY: RefCell<DetHashMap<Plan, Lane>> = RefCell::new(DetHashMap::default());
}

/// The lane that printed `plan`'s document at an earlier render on this
/// thread, if one after the direct lane did.
pub(super) fn printed_by(plan: &Plan) -> Option<Lane> {
    if crate::resolution_dag_memo::memo_disabled() {
        return None;
    }
    PRINTED_BY.with(|printed| printed.borrow().get(plan).copied())
}

/// Record that `lane` printed `plan`'s document; nothing for a small
/// circuit, which has no plan because it has no lanes to skip.
pub(super) fn remember(plan: Option<Plan>, lane: Lane) {
    let Some(plan) = plan else {
        return;
    };
    PRINTED_BY.with(|printed| {
        let mut printed = printed.borrow_mut();
        if printed.len() >= MAX_PLANS {
            printed.clear();
        }
        printed.insert(plan, lane);
    });
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_plan_is_sent_to_the_lane_that_printed_it_and_no_other_plan_is() {
        let literal = |index: usize| Literal::from_index(index);
        let cnf = vec![vec![literal(0), literal(3)], vec![literal(1)]];
        let plan = Plan::of(2, &cnf);
        assert_eq!(printed_by(&plan), None);
        remember(Some(plan), Lane::Cases);
        assert_eq!(printed_by(&Plan::of(2, &cnf)), Some(Lane::Cases));
        // Another clause set, or the same clauses over more gates, is another
        // plan.
        assert_eq!(printed_by(&Plan::of(2, &cnf[..1])), None);
        assert_eq!(printed_by(&Plan::of(3, &cnf)), None);
        remember(Some(plan), Lane::Sweep);
        assert_eq!(printed_by(&plan), Some(Lane::Sweep));
        remember(None, Lane::Cases);
        assert_eq!(printed_by(&plan), Some(Lane::Sweep));
    }
}
