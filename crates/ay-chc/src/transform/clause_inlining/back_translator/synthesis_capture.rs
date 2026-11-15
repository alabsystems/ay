// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Test-only observation of a named definition on the real translator stack.
//!
//! Earlier definitions retain their existing exact/legacy behavior. The target
//! is captured before projection and must close exactly, so a failing regression
//! stops before its expensive legacy enumeration. This is not a no-SMT harness.

use super::{exact_projection, ChcProblem, HornClause, InliningBackTranslator};
use crate::{ChcExpr, ChcVar, ClauseHead, PredicateInterpretation};
use ay_core::time::Instant;
use std::cell::RefCell;
use std::sync::Arc;

#[derive(Clone)]
struct Stage {
    ordinal: usize,
    definitions: usize,
    input: Option<Arc<ChcProblem>>,
}

struct Capture {
    target: &'static str,
    deadline: Instant,
    next_stage: usize,
    stage: Option<Stage>,
    definition: Option<HornClause>,
    observations: Vec<Observation>,
}

struct Observation {
    stage: usize,
    definitions: usize,
    clause: HornClause,
    keep: Vec<ChcVar>,
    formula: ChcExpr,
}

thread_local! {
    static CAPTURE: RefCell<Option<Capture>> = const { RefCell::new(None) };
}

struct CaptureGuard(Option<Capture>);

impl CaptureGuard {
    fn install(target: &'static str, deadline: Instant) -> Self {
        Self(CAPTURE.with(|cell| {
            cell.replace(Some(Capture {
                target,
                deadline,
                next_stage: 0,
                stage: None,
                definition: None,
                observations: Vec::new(),
            }))
        }))
    }

    fn take(&self) -> Vec<Observation> {
        CAPTURE.with(|cell| std::mem::take(&mut cell.borrow_mut().as_mut().unwrap().observations))
    }
}

impl Drop for CaptureGuard {
    fn drop(&mut self) {
        let previous = self.0.take();
        let _ = CAPTURE.try_with(|cell| cell.replace(previous));
    }
}

pub(super) struct StageGuard(Option<Option<Stage>>);

impl Drop for StageGuard {
    fn drop(&mut self) {
        if let Some(previous) = self.0.take() {
            let _ = CAPTURE.try_with(|cell| {
                if let Some(capture) = cell.borrow_mut().as_mut() {
                    capture.stage = previous;
                }
            });
        }
    }
}

pub(super) fn enter_stage(translator: &InliningBackTranslator) -> StageGuard {
    StageGuard(CAPTURE.with(|cell| {
        let mut state = cell.borrow_mut();
        let capture = state.as_mut()?;
        assert!(Instant::now() < capture.deadline, "capture deadline");
        capture.next_stage += 1;
        let next = Stage {
            ordinal: capture.next_stage,
            definitions: translator.inlined_defs.len(),
            input: translator.input_problem.clone(),
        };
        Some(capture.stage.replace(next))
    }))
}

pub(super) struct DefinitionGuard(Option<Option<HornClause>>);

impl Drop for DefinitionGuard {
    fn drop(&mut self) {
        if let Some(previous) = self.0.take() {
            let _ = CAPTURE.try_with(|cell| {
                if let Some(capture) = cell.borrow_mut().as_mut() {
                    capture.definition = previous;
                }
            });
        }
    }
}

pub(super) fn enter_definition(clause: &HornClause) -> DefinitionGuard {
    DefinitionGuard(CAPTURE.with(|cell| {
        let mut state = cell.borrow_mut();
        let capture = state.as_mut()?;
        assert!(Instant::now() < capture.deadline, "capture deadline");
        let selected = capture
            .stage
            .as_ref()
            .and_then(|stage| stage.input.as_ref())
            .and_then(|input| match &clause.head {
                ClauseHead::Predicate(id, _) => input.get_predicate(*id),
                ClauseHead::False => None,
            })
            .is_some_and(|predicate| predicate.name == capture.target);
        Some(std::mem::replace(
            &mut capture.definition,
            selected.then(|| clause.clone()),
        ))
    }))
}

pub(super) fn before_projection(interpretation: &PredicateInterpretation) {
    CAPTURE.with(|cell| {
        let mut state = cell.borrow_mut();
        let Some(capture) = state.as_mut() else {
            return;
        };
        assert!(Instant::now() < capture.deadline, "capture deadline");
        let Some(clause) = capture.definition.as_ref() else {
            return;
        };
        let stage = capture.stage.as_ref().unwrap();
        let nodes = interpretation.formula.node_count(65_537);
        assert!(nodes <= 65_536, "bounded test capture");
        assert!(capture.observations.len() < 32, "bounded capture count");
        eprintln!(
            "consumer reconstruction target={} inlining_stage={} definitions={} clause={clause:?} keep={:?} nodes={nodes} formula={:?}",
            capture.target,
            stage.ordinal,
            stage.definitions,
            interpretation.vars,
            interpretation.formula,
        );
        capture.observations.push(Observation {
            stage: stage.ordinal,
            definitions: stage.definitions,
            clause: clause.clone(),
            keep: interpretation.vars.clone(),
            formula: interpretation.formula.clone(),
        });
    });
}

pub(super) fn after_projection(projection: &exact_projection::Projection) {
    CAPTURE.with(|cell| {
        let state = cell.borrow();
        let Some(capture) = state.as_ref() else {
            return;
        };
        assert!(Instant::now() < capture.deadline, "capture deadline");
        if capture.definition.is_some() {
            let outcome = match projection {
                exact_projection::Projection::Closed(_) => "closed",
                exact_projection::Projection::Declined => "declined",
                exact_projection::Projection::Stopped => "stopped",
            };
            assert!(
                matches!(projection, exact_projection::Projection::Closed(_)),
                "named original definition {} exact projection {outcome}; captured before legacy fallback",
                capture.target,
            );
        }
    });
}

mod consumer;
mod realloc;
