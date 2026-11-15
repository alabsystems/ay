// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//! Raw same-solve hints; no certificate or verdict is produced here.
use super::*;

/// Untrusted primal and dual hints from one optimal-status float candidate.
///
/// This is NOT an [`Outcome`], a witness, an exact bound, or a certificate.
/// Float optimal status supplies no proof of feasibility or optimality. A
/// caller must independently validate any claim it derives from either field.
#[derive(Debug, PartialEq)]
pub struct FloatLpAdvice {
    /// Original model columns, indexed by [`Col::index`], in the original
    /// unscaled frame. Internal logical/slack columns are never included.
    ///
    /// `None` means the original prefix was short, nonfinite, or expired
    /// during capture; the usual dual hint is still retained. Values are not
    /// clamped to bounds or rounded to integrality. Even a finite point can
    /// violate the model. A successful box has exactly `model.num_cols()`
    /// elements, not the capacity of the internal simplex vector.
    pub primal: Option<Box<[f64]>>,
    /// The same raw dual vector returned by
    /// [`LpSession::float_dual_for_expr`], with exactly its existing sign and
    /// numerical conventions. It is moved, not rescanned or copied here.
    /// Its allocation capacity can exceed its length.
    pub duals: Vec<f64>,
}

impl LpSession {
    /// Obtain original-column primal advice and the usual duals from the SAME
    /// float solve. No exact solve, retry, witness check, or new LP is run.
    ///
    /// Outer `None` has the same conditions as [`Self::float_dual_for_expr`]:
    /// empty form, disabled/unavailable float lane, or non-optimal float status.
    /// A declined primal capture retains the candidate's duals in `Some`.
    /// Maximization uses the same negated-objective convention as the old API.
    ///
    /// The existing absolute solve deadline also bounds primal capture; it is
    /// not renewed after the solve. Capture checks it before and after the
    /// finite scan and after the bounded copy. These checks are cooperative,
    /// so a copy already started can finish after the deadline and be discarded.
    ///
    /// EXTRA COST: for `n = model.num_cols()`, at most `n` finiteness checks
    /// plus one `n`-element copy. Logical suffix values are not visited. A
    /// successful primal owns nominal payload `8*n` bytes, excluding allocator
    /// overhead. During capture, the old full candidate and the new prefix
    /// coexist. The raw dual allocation is moved unchanged. Callers with work
    /// or payload caps must admit these costs BEFORE calling this method;
    /// a later refusal does not undo work. The old dual-only API does none of
    /// this prefix scanning or copying.
    ///
    /// # Errors
    /// [`MilpError::Session`] for an out-of-range column or nonfinite objective
    /// weight, under exactly the existing dual-only input validation.
    pub fn float_advice_for_expr(
        &mut self,
        expr: &[(Col, f64)],
        sense: Sense,
    ) -> Result<Option<FloatLpAdvice>, MilpError> {
        let Some((candidate, deadline)) = self.float_candidate_for_expr(expr, sense)? else {
            return Ok(None);
        };
        Ok(Some(FloatLpAdvice::from_candidate(
            candidate,
            self.model.num_cols(),
            deadline,
        )))
    }

    /// The previous dual-only implementation, with the candidate and the
    /// exact deadline passed to its sole solve retained for the new caller.
    pub(super) fn float_candidate_for_expr(
        &mut self,
        expr: &[(Col, f64)],
        sense: Sense,
    ) -> Result<Option<(Candidate, Option<Instant>)>, MilpError> {
        for (col, w) in expr {
            if col.index() >= self.model.num_cols() {
                return Err(MilpError::Session {
                    message: format!("column {} out of range", col.index()),
                });
            }
            if !w.is_finite() {
                return Err(MilpError::Session {
                    message: "non-finite objective weight".to_string(),
                });
            }
        }
        if expr.is_empty() || !float_lane_enabled(&self.opts) {
            return Ok(None);
        }
        let scale = match sense {
            Sense::Minimize => 1.0_f64,
            Sense::Maximize => -1.0_f64,
        };
        let scaled: Vec<(u32, f64)> = expr.iter().map(|(c, w)| (c.0, w * scale)).collect();
        let Some(mut lp) = self.float_lp(&scaled, Sense::Minimize) else {
            return Ok(None);
        };
        lp.plain_cold = true;
        let deadline = self.opts.effective_deadline(Instant::now());
        #[cfg(test)]
        OBSERVATIONS.with(|o| o.set((o.get().0 + 1, o.get().1)));
        let candidate = lp.solve(deadline);
        if candidate.status != SimplexStatus::Optimal {
            return Ok(None);
        }
        Ok(Some((candidate, deadline)))
    }
}

impl FloatLpAdvice {
    fn from_candidate(candidate: Candidate, columns: usize, deadline: Option<Instant>) -> Self {
        Self {
            primal: original_prefix(&candidate.values, columns, deadline),
            duals: candidate.duals,
        }
    }
}

fn expired(deadline: Option<Instant>) -> bool {
    deadline.is_some_and(|end| Instant::now() >= end)
}

fn original_prefix(
    values: &[f64],
    columns: usize,
    deadline: Option<Instant>,
) -> Option<Box<[f64]>> {
    if expired(deadline) {
        return None;
    }
    let prefix = values.get(..columns)?;
    if prefix.iter().any(|x| !x.is_finite()) || expired(deadline) {
        return None;
    }
    #[cfg(test)]
    OBSERVATIONS.with(|o| o.set((o.get().0, o.get().1 + 1)));
    let primal = Box::<[f64]>::from(prefix);
    (!expired(deadline)).then_some(primal)
}

// Thread-local counts observe real calls and prefix allocations, without
// solver-global state or changing non-test builds.
#[cfg(test)]
std::thread_local! {
    static OBSERVATIONS: std::cell::Cell<(usize, usize)> = const {
        std::cell::Cell::new((0, 0))
    };
}

#[cfg(test)]
#[path = "float_advice_tests.rs"]
mod tests;
