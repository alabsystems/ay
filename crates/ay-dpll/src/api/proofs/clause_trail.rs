// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Immutable, context-local snapshots of actual clause lifecycle events.

use crate::api::{Solver, Term};
use ay_sat::ClauseEventOrigin;

/// Native event origin, independent of the final refutation's rule kinds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NativeClauseOrigin {
    /// Boolean input encoding.
    Assumption,
    /// Boolean learned clause.
    Lemma,
    /// Unconditional theory axiom.
    TheoryAssumption,
    /// Theory conflict or propagation.
    TheoryLemma,
    /// Actual retirement of a stored clause.
    Deleted,
}

/// One actual insertion or retirement. No reconstructed proof is claimed by this event.
#[derive(Clone, Debug)]
pub struct NativeClauseEvent {
    /// Event classification supplied by the producing solver.
    pub origin: NativeClauseOrigin,
    /// Signed context-local literals in the recorded order.
    pub literals: Vec<Term>,
}

/// Immutable snapshot for one completed UNSAT check.
#[derive(Clone, Debug)]
pub struct NativeClauseTrail {
    /// Insertion and retirement events in their original order.
    pub events: Vec<NativeClauseEvent>,
}

impl Solver {
    /// Internal per-check artifact policy; ordinary proof replay stays addition-only.
    #[doc(hidden)]
    pub fn set_clause_event_capture(&mut self, policy: ay_sat::ClauseEventCapture) {
        self.executor.clause_event_capture = policy;
    }

    /// Current internal artifact capture request.
    #[doc(hidden)]
    pub fn clause_event_capture(&self) -> ay_sat::ClauseEventCapture {
        self.executor.clause_event_capture
    }

    /// Snapshot the native clause lifecycle trace using authenticated local terms.
    /// Missing literal mappings or an incomplete trace refuse the whole view.
    #[doc(hidden)]
    pub fn native_clause_trail(&mut self) -> Option<NativeClauseTrail> {
        let trace = self.executor.native_clause_trace()?;
        if !trace.captures_full_lifecycle()
            || trace.is_truncated()
            || trace.proof_work_exhausted()
            || trace.len() > 65_536
        {
            return None;
        }
        let mapping = self.executor.last_var_to_term()?;
        let mut count = 0usize;
        let mut records = Vec::with_capacity(trace.len());
        for event in trace.events() {
            if records.len() >= 65_536 {
                return None;
            }
            count = count.checked_add(event.clause.len())?;
            if count > 262_144 {
                return None;
            }
            let literals = event
                .clause
                .iter()
                .map(|literal| {
                    let term = *mapping.get(&(literal.variable().index() as u32))?;
                    self.terms().entry_stamp(term)?;
                    Some((self.wrap_term(term), literal.is_positive()))
                })
                .collect::<Option<Vec<_>>>()?;
            let origin = match event.origin {
                ClauseEventOrigin::Assumption => NativeClauseOrigin::Assumption,
                ClauseEventOrigin::Lemma => NativeClauseOrigin::Lemma,
                ClauseEventOrigin::TheoryAssumption => NativeClauseOrigin::TheoryAssumption,
                ClauseEventOrigin::TheoryLemma => NativeClauseOrigin::TheoryLemma,
                ClauseEventOrigin::Deleted => NativeClauseOrigin::Deleted,
            };
            records.push((origin, literals));
        }
        let events = records
            .into_iter()
            .map(|(origin, literals)| {
                let literals = literals
                    .into_iter()
                    .map(|(term, positive)| {
                        if positive {
                            Some(term)
                        } else {
                            self.try_not(term).ok()
                        }
                    })
                    .collect::<Option<Vec<_>>>()?;
                Some(NativeClauseEvent { origin, literals })
            })
            .collect::<Option<Vec<_>>>()?;
        Some(NativeClauseTrail { events })
    }
}
