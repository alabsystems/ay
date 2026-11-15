// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The two checks of a goal that reaches quantified well-formedness guards
//! (see the parent module).

use ay_dpll::api::Term;

use super::WfObligations;
use crate::z3_compat::Z3Context;

/// How a check treats the quantified guards of the symbols its goal reaches
/// (see the module docs). The first check of a goal without a binder leaves
/// them out and validates a SAT model against them. A goal with a binder is
/// checked with them first, as before validation existed: its SAT path
/// certifies a quantified model, a cost a model that then fails validation
/// wastes (measured: repeated `Exists x. code(A[x]) > 196607` checks in one
/// context grew from 0.02 s to 3 s each in that certificate). When the first
/// check answers `unknown`, or its relaxed model is not a model of the
/// guards, the goal is checked once more in the other mode.
#[derive(Default)]
pub(crate) struct WfPhase {
    /// Whether this check asserts the quantified guards; `None` until a
    /// first check picks it from its goal.
    assert_quantified_guards: Option<bool>,
    /// Whether this is the second check of the goal (no third follows).
    second: bool,
    /// Set by a first check that needs the second.
    pub(crate) recheck: bool,
}

impl WfPhase {
    /// A check that asserts every guard and is followed by no other.
    pub(crate) fn guarded() -> WfPhase {
        WfPhase {
            assert_quantified_guards: Some(true),
            second: true,
            recheck: false,
        }
    }

    /// The check that follows this one, in the other mode.
    pub(crate) fn next(&self) -> WfPhase {
        WfPhase {
            assert_quantified_guards: Some(!self.asserts_quantified_guards()),
            second: true,
            recheck: false,
        }
    }

    /// Whether this check asserts the quantified guards.
    pub(crate) fn asserts_quantified_guards(&self) -> bool {
        self.assert_quantified_guards.unwrap_or(true)
    }

    /// The guards this check asserts; a first check picks its mode here.
    pub(crate) fn guards(&mut self, obligations: &WfObligations) -> Vec<Term> {
        let assert = *self
            .assert_quantified_guards
            .get_or_insert(obligations.binder);
        let mut guards = obligations.eager.clone();
        if assert {
            guards.extend(obligations.lazy.iter().copied());
        }
        guards
    }

    /// Whether the goal may be checked again in the other mode.
    pub(crate) fn may_recheck(&self, obligations: &WfObligations) -> bool {
        !self.second && !obligations.lazy.is_empty()
    }

    /// The timeout of a relaxed first check that a guarded one may follow:
    /// half of `timeout`, so the guarded check keeps the other half (measured:
    /// in a context that many earlier checks filled with range axioms,
    /// `Distinct(C[0], C[1], C[2], C[3])` over `Array(Int, FD(3))` took 3.8 s
    /// relaxed, and timed out at 20 s after more checks, where the guarded
    /// check took 0.4 s). `None` when the check keeps `timeout`.
    pub(crate) fn first_check_timeout(
        &self,
        obligations: &WfObligations,
        timeout: Option<std::time::Duration>,
    ) -> Option<std::time::Duration> {
        let relaxed = !self.asserts_quantified_guards() && self.may_recheck(obligations);
        timeout
            .filter(|_| relaxed)
            .map(|timeout| (timeout / 2).max(std::time::Duration::from_millis(1)))
    }

    /// Record a check that answered `unknown`: the other mode may decide.
    pub(crate) fn note_undecided(&mut self, obligations: &WfObligations) {
        if self.may_recheck(obligations) {
            self.recheck = true;
        }
    }
}

/// Whether the second check is due (see [`WfPhase`]): the first check asked
/// for it, was not interrupted, and left some of its timeout.
pub(crate) fn recheck_due(ctx: &Z3Context, phase: &WfPhase, started: std::time::Instant) -> bool {
    phase.recheck
        && !ctx.solver.is_interrupted()
        && ctx
            .solver
            .timeout()
            .is_none_or(|timeout| started.elapsed() < timeout)
}
