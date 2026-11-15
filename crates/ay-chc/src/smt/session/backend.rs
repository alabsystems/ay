// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `Backend` — the A/B harness trait (design §2.2; contract C7; owner WP-1 / A).
//!
//! Object-safe so the harness can replay ONE query stream on either arm:
//! `HornSmt` (the session) or the control arm `DpllFreshBackend` (WP-4,
//! optional for the Rung-1 exit) that answers each check with a FRESH
//! `ay_dpll::api::Solver` over the conjunction of the active exprs — the
//! configuration the microbenchmark measured sound (0 disagreements / 2,484
//! verdicts). The control arm returns no Farkas.

use std::sync::Arc;
use std::time::Duration;

use ay_core::kani_compat::DetHashMap as FxHashMap;

use super::{AssertId, HornCheck, HornSmt, SessionStats, UnknownReason};
use crate::smt::types::{FarkasConflict, Partition, SmtValue};
use crate::ChcExpr;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BackendKind {
    Session,
    DpllFresh,
}

pub(crate) trait Backend {
    fn assert_persistent(
        &mut self,
        c: &Arc<ChcExpr>,
        p: Partition,
    ) -> Result<AssertId, UnknownReason>;
    fn push(&mut self);
    fn pop(&mut self) -> bool;
    fn check_assuming(
        &mut self,
        assuming: &[AssertId],
        extra: &[Arc<ChcExpr>],
        budget: Option<Duration>,
    ) -> HornCheck;
    fn check_conjunction(
        &mut self,
        expr: &ChcExpr,
        budget: Option<Duration>,
        phase_seed: Option<&FxHashMap<String, SmtValue>>,
    ) -> HornCheck;
    fn value(&self, expr: &ChcExpr) -> Option<SmtValue>;
    fn farkas_for_last_unsat(&mut self, a: &[AssertId], b: &[AssertId]) -> Vec<FarkasConflict>;
    fn stats(&self) -> &SessionStats;
    fn kind(&self) -> BackendKind;
}

impl Backend for HornSmt {
    fn assert_persistent(
        &mut self,
        c: &Arc<ChcExpr>,
        p: Partition,
    ) -> Result<AssertId, UnknownReason> {
        HornSmt::assert_persistent(self, c, p)
    }

    fn push(&mut self) {
        HornSmt::push(self);
    }

    fn pop(&mut self) -> bool {
        HornSmt::pop(self)
    }

    fn check_assuming(
        &mut self,
        assuming: &[AssertId],
        extra: &[Arc<ChcExpr>],
        budget: Option<Duration>,
    ) -> HornCheck {
        HornSmt::check_assuming(self, assuming, extra, budget)
    }

    fn check_conjunction(
        &mut self,
        expr: &ChcExpr,
        budget: Option<Duration>,
        phase_seed: Option<&FxHashMap<String, SmtValue>>,
    ) -> HornCheck {
        HornSmt::check_conjunction(self, expr, budget, phase_seed)
    }

    fn value(&self, expr: &ChcExpr) -> Option<SmtValue> {
        HornSmt::value(self, expr)
    }

    fn farkas_for_last_unsat(&mut self, a: &[AssertId], b: &[AssertId]) -> Vec<FarkasConflict> {
        HornSmt::farkas_for_last_unsat(self, a, b)
    }

    fn stats(&self) -> &SessionStats {
        HornSmt::stats(self)
    }

    fn kind(&self) -> BackendKind {
        BackendKind::Session
    }
}
