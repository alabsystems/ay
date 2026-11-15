// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The monolithic refutation inside a counted work envelope, and the one
//! refusal this memo keeps.
//!
//! Everywhere else this memo keeps successes only: a deadline or a stop can
//! decline what a later ask would refute, and replaying such a decline would
//! let timing decide a document. An envelope's refusal is counted instead, in
//! solver conflicts and decisions, which do not steer the search, and it was
//! paid in full at every ask: one publication asks the support question
//! several times over and renders the lemma again at export. So a
//! [`ResolutionDagError::OverEnvelope`] IS retained, under the CNF and the
//! envelope, and a repeated ask is answered at once.
//!
//! The count is as reproducible as the search, and the first attempt's
//! inprocessing is scheduled by wall-clock caps unless
//! `--sat-deterministic-inproc` is set (`ay_sat`'s `determinism.rs`): a CNF
//! at the envelope's very edge may refute at one ask and not at another.
//! Retained, the first answer is every later ask's in the process, so the
//! support question and the render agree; a refutation stored by any ask
//! still wins over a refusal.
//!
//! A refusal is a CNF's fingerprint, not the CNF: a refused circuit is the
//! large one, and its clauses are already the success table's to hold when
//! some other ask refutes it. A retained refusal only ever declines — the
//! caller falls back to the unproved step it would have printed anyway — so
//! a colliding fingerprint can cost a document, never admit one. A stop
//! ([`ResolutionDagError::Unknown`]) is never retained.

use super::{lookup, memo_disabled, store, MemoKey};
use ay_core::kani_compat::DetHashSet;
use ay_sat::{
    prove_unsat_resolution_dag_within, Literal, ResolutionDag, ResolutionDagError,
    ResolutionDagWork,
};
use std::cell::{Cell, RefCell};
use std::hash::{Hash, Hasher};

#[cfg(test)]
#[path = "within_tests.rs"]
mod tests;

/// Refusals retained before the record is dropped wholesale.
const MAX_REFUSALS: usize = 4_096;

/// A refused CNF under the envelope that refused it.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Refusal {
    num_vars: usize,
    clauses: usize,
    fingerprint: u64,
    work: ResolutionDagWork,
}

impl Refusal {
    fn of(num_vars: usize, clauses: &[Vec<Literal>], work: ResolutionDagWork) -> Self {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        clauses.hash(&mut hasher);
        Self {
            num_vars,
            clauses: clauses.len(),
            fingerprint: hasher.finish(),
            work,
        }
    }
}

#[derive(Default)]
struct Refusals {
    refused: DetHashSet<Refusal>,
    served: u64,
}

thread_local! {
    static REFUSALS: RefCell<Refusals> = RefCell::new(Refusals::default());
}

/// [`prove_unsat_resolution_dag_within`], served from the per-thread memo: a
/// refutation under the key of [`super::prove_unsat_resolution_dag_memoized`]
/// (the envelope only bounds work, so a refutation of this CNF, however it
/// was found, is one), and an envelope's refusal from the refusal record.
///
/// `should_stop` is consulted BEFORE a refutation is served: a stopped
/// caller observes a stop, never a refutation.
///
/// # Errors
/// Exactly [`prove_unsat_resolution_dag_within`]'s. Only
/// [`ResolutionDagError::OverEnvelope`] is retained.
pub fn prove_unsat_resolution_dag_memoized_within(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    work: ResolutionDagWork,
    should_stop: Option<&dyn Fn() -> bool>,
) -> Result<ResolutionDag, ResolutionDagError> {
    let stopped = Cell::new(false);
    let stop = || {
        if stopped.replace(true) {
            return true;
        }
        let refused = should_stop.is_some_and(|stop| stop());
        stopped.set(refused);
        refused
    };
    let observe = || {
        if stop() {
            Err(ResolutionDagError::Unknown)
        } else {
            Ok(())
        }
    };
    observe()?;
    if memo_disabled() {
        let result = prove_unsat_resolution_dag_within(num_vars, clauses, work, Some(&stop));
        if result.is_ok() {
            observe()?;
        }
        return result;
    }
    let key = MemoKey {
        num_vars,
        clauses: clauses.to_vec(),
        limits: None,
        strategy: None,
    };
    observe()?;
    if let Some(dag) = lookup(&key) {
        observe()?;
        return Ok(dag);
    }
    observe()?;
    let refusal = Refusal::of(num_vars, clauses, work);
    observe()?;
    let refused = REFUSALS.with(|record| {
        let mut record = record.borrow_mut();
        let refused = record.refused.contains(&refusal);
        record.served += u64::from(refused);
        refused
    });
    observe()?;
    if refused {
        return Err(ResolutionDagError::OverEnvelope);
    }
    match prove_unsat_resolution_dag_within(num_vars, clauses, work, Some(&stop)) {
        Ok(dag) => {
            observe()?;
            store(key, &dag);
            observe()?;
            Ok(dag)
        }
        Err(ResolutionDagError::OverEnvelope) => {
            observe()?;
            REFUSALS.with(|record| {
                let mut record = record.borrow_mut();
                if record.refused.len() >= MAX_REFUSALS {
                    record.refused.clear();
                }
                record.refused.insert(refusal);
            });
            observe()?;
            Err(ResolutionDagError::OverEnvelope)
        }
        Err(error) => Err(error),
    }
}

/// Refusals this thread has served from the record, for tests and
/// measurement.
#[must_use]
pub fn resolution_dag_refusals_served() -> u64 {
    REFUSALS.with(|record| record.borrow().served)
}

/// Drop every retained refusal on this thread.
pub(super) fn reset_refusals() {
    REFUSALS.with(|record| *record.borrow_mut() = Refusals::default());
}
