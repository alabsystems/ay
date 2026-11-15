// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #abv-subst-model-retry: when the preprocessing-free re-solve is armed.
//!
//! The eager BV lane builds its model through the recovery of the variables
//! that preprocessing substituted away. When the gates do not accept that
//! model, the same original assertions solved without preprocessing can give
//! a model they do accept. That holds whatever the gate said about the first
//! model. A refutation is one case: a select whose index mentions an
//! eliminated variable loses its link to the bit-blasted read. A model the
//! validator could not evaluate is another. `purify_bool_args` gives `(h b)`
//! a proxy `p` defined by `(= p b)`, substitution puts `b` back for `p`, and
//! `b` then occurs only as an argument, so the solve never assigns it and
//! `(h boolarg_13)` evaluates to Unknown.
//!
//! Keeping such proxies out of the substitution closes that case without a
//! second solve. Measured on the store-chain fuzz sets, it lost sats and
//! printed models elsewhere: proxies hid array operands from the array model,
//! and array-equality keys of printed tables became unevaluable. So the case
//! is left to this re-solve.
//!
//! The arm used to fire only on the refuting oracles, so its trigger depended
//! on how the rejection was worded. On fzN1 q8811_118 the base model was
//! refuted by `arrays-read-conflict-uneval` and the retry answered `sat`.
//! Once the store-chain work let that model reach the Bool proxy, it became
//! an `incomplete` rejection, the retry never fired, and the answer degraded
//! to `unknown`.

use super::*;

impl Executor {
    /// Whether a check-sat that answered `result` gets the single
    /// preprocessing-free re-solve.
    ///
    /// Two signals arm it. `bv_subst_model_rejected` is set by the in-loop BV
    /// validator, the strict oracle and the independent gate, including every
    /// independent-gate or SAT-emission downgrade (`downgrade_sat_after_gate`).
    /// `model_validation_failures` counts every validation-pipeline rejection
    /// of a candidate, whatever its reason, and it arms the retry while the
    /// solve that built the candidate ran substitution (`bv_subst_lane`). The
    /// #array-refutation-retry arm reads the same counter.
    ///
    /// SOUND: the re-solve decides the identical assertion set with fewer
    /// preprocessing transforms, and its verdict goes through
    /// `emit_sat_verdict`, so every gate runs again. A model the gates still
    /// reject stays the fail-closed `unknown`. The re-solve fires at most once
    /// per check-sat, and never after a timeout or past the deadline.
    ///
    /// COST: the re-solve runs with no preprocessing at all, so it can cost far
    /// more than the solve it repeats (a long definitional chain that
    /// preprocessing folds to constants is bit-blasted in full). Only the
    /// deadline and the memory budget, when set, bound it, as for any solve.
    pub(super) fn bv_subst_retry_armed(&self, result: &SolveResult) -> bool {
        *result == SolveResult::Unknown
            && (self.bv_subst_model_rejected
                || (self.bv_subst_lane && self.last_statistics.model_validation_failures > 0))
            && !self.bv_subst_retry_done
            && !matches!(self.last_unknown_reason, Some(UnknownReason::Timeout))
            && !self.solve_deadline.expired()
    }
}

#[cfg(test)]
mod tests;
