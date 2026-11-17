// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use std::collections::VecDeque;

pub(super) fn source() -> QuantifiedChcProblem {
    QuantifiedChcProblem::parse_smtlib(
        "(declare-var a (Array (_ BitVec 8) Bool))
         (declare-rel P ((Array (_ BitVec 8) Bool)))
         (declare-rel error_p0 ())(declare-rel error_p1 ())(declare-rel error ())
         (rule (=> (forall ((i (_ BitVec 8))) (= (select a i) true)) (P a)))
         (rule (=> (and (P a) (not (select a (_ bv0 8)))) error_p0))
         (rule (=> (and (P a) (not (select a (_ bv1 8)))) error_p1))
         (rule (=> error_p0 error))(rule (=> error_p1 error))(query error)",
    )
    .expect("two source-preserving property rows")
}

pub(super) fn obligations() -> Vec<QuantifiedChcQueryObligation> {
    source()
        .query_obligations(Duration::from_secs(10), &CancellationToken::new())
        .expect("source decomposition")
}

#[derive(Clone, Copy)]
pub(super) enum Candidate {
    Good,
    Foreign,
    Unknown,
    Error,
    CancelReset,
}

#[derive(Clone, Copy)]
pub(super) enum Replay {
    Good,
    Rejected,
    Error,
    CancelReset,
}

#[derive(Clone, Copy)]
pub(super) struct Action {
    pub candidate: Candidate,
    pub solve_time: Duration,
    pub replay: Replay,
    pub replay_time: Duration,
}

impl Default for Action {
    fn default() -> Self {
        Self {
            candidate: Candidate::Good,
            solve_time: Duration::from_secs(2),
            replay: Replay::Good,
            replay_time: Duration::from_secs(1),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(super) enum Call {
    Solve(Duration, Option<usize>),
    Replay(Duration),
}

pub(super) struct Fake<'a> {
    pub time: &'a Cell<Duration>,
    pub parent: &'a CancellationToken,
    pub actions: VecDeque<Action>,
    pub calls: Vec<Call>,
    current: Action,
}

impl<'a> Fake<'a> {
    pub(super) fn new(
        time: &'a Cell<Duration>,
        parent: &'a CancellationToken,
        actions: Vec<Action>,
    ) -> Self {
        Self {
            time,
            parent,
            actions: actions.into(),
            calls: Vec::new(),
            current: Action::default(),
        }
    }

    fn cancel_reset(&self, token: &CancellationToken) {
        self.parent.cancel();
        assert!(token.child().child().is_cancelled());
        self.parent.reset();
        assert!(!self.parent.is_cancelled());
    }
}

impl runner::Runner for Fake<'_> {
    type Evidence = String;

    fn solve(
        &mut self,
        problem: &QuantifiedChcProblem,
        budget: Duration,
        memory: Option<usize>,
        token: &CancellationToken,
    ) -> crate::Result<Option<String>> {
        self.calls.push(Call::Solve(budget, memory));
        self.current = self
            .actions
            .pop_front()
            .expect("one configured action per solve");
        self.time.set(self.time.get() + self.current.solve_time);
        match self.current.candidate {
            Candidate::Good => Ok(Some(problem.source_smtlib().to_owned())),
            Candidate::Foreign => Ok(Some("not this source".into())),
            Candidate::Unknown => Ok(None),
            Candidate::Error => {
                Err(ay_chc::ChcError::Internal("ordinary solve error".into()).into())
            }
            Candidate::CancelReset => {
                self.cancel_reset(token);
                Ok(Some(problem.source_smtlib().to_owned()))
            }
        }
    }

    fn source<'a>(&self, evidence: &'a String) -> &'a str {
        evidence
    }

    fn recheck(
        &mut self,
        _: &String,
        _: &QuantifiedChcProblem,
        budget: Duration,
        token: &CancellationToken,
    ) -> crate::Result<bool> {
        self.calls.push(Call::Replay(budget));
        self.time.set(self.time.get() + self.current.replay_time);
        match self.current.replay {
            Replay::Good => Ok(true),
            Replay::Rejected => Ok(false),
            Replay::Error => Err(ay_chc::ChcError::Internal("ordinary replay error".into()).into()),
            Replay::CancelReset => {
                self.cancel_reset(token);
                Ok(true)
            }
        }
    }
}
