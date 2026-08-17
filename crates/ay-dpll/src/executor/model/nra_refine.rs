// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Rational refinement of algebraic NRA model values at model-print time
//! (#nra-rational-refinement).
//!
//! PROBLEM (measured, mvnra-full): AY prints irrational NRA witnesses in z3's
//! `root-obj` syntax — e.g. `(define-fun skoC () Real (root-obj (+ (* 4 (^ x
//! 2)) (- 3)) 1))` — which is NOT SMT-LIB, so external model validators
//! (dolmen) fail with a parse error on every such model (218/2037 sat models
//! in the MV QF_NonLinearRealArith run).
//!
//! FIX (decline-only): before `(get-model)` renders a model that contains
//! algebraic values, run ONE bounded search for a fully rational substitute
//! assignment. It has two stages, sharing this module's verification and
//! rollback machinery:
//!
//!   * JOINT ([`joint`], #nra-joint-refinement) — when the algebraic value is
//!     pinned by an equality coupling it to rational partners
//!     (`skoS² + skoC² = 1`), the partners MOVE WITH IT along the pinning
//!     variety. Nothing else can reach those models: with the partners held
//!     fixed the equality forces the irrational value. It runs first, on the
//!     widest intervals, because its candidates carry the isolating interval's
//!     precision into their denominators.
//!   * PER-VALUE (below) — the algebraic values move alone to the simplest
//!     nearby rationals. This reaches everything whose constraints are open
//!     around the model point.
//!
//! The per-value search:
//!
//!   1. Each irrational value contributes its exact isolating interval.
//!      Candidates are the SIMPLEST rational (smallest denominator, via the
//!      Stern-Brocot / continued-fraction walk) in the current interval;
//!      between rounds every interval is narrowed by exact bisection against
//!      the algebraic value, so candidates converge toward the true root with
//!      the smallest denominators first.
//!   2. A candidate assignment is installed and EVERY assertion is re-checked
//!      with the exact model evaluator (`evaluate_term`, plain BigRational
//!      arithmetic once all values are rational) — the same machinery model
//!      validation uses. Only `Bool(true)` on every assertion accepts.
//!   3. On acceptance the rational assignment IS the model (get-model and
//!      get-value both read it). On decline the original algebraic model is
//!      restored bit-for-bit and prints exactly as before: a `root-obj` model
//!      that fails external parse is still better than a WRONG rational model.
//!
//! BOUNDS: rounds, per-round bisection steps, the Stern-Brocot walk depth and
//! the candidate numerator/denominator size are all hard-capped, so the
//! search cannot hang a solve. It runs at most once per SAT verdict
//! (`nra_print_refinement_attempted`), and only when algebraic values are
//! present.

use std::cmp::Ordering;

use ay_core::kani_compat::DetHashMap;
use ay_core::TermId;
use ay_lra::LraModel;
use ay_nra::{RealAlgebraic, RealAlgebraicValue, RealScalar};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

use super::EvalValue;
use crate::executor::Executor;
use crate::executor_types::SolveResult;

/// Candidate assignments attempted (one exact full-model re-check each).
const MAX_REFINE_ROUNDS: usize = 12;

/// Exact bisection steps narrowing each value's interval between rounds.
const BISECT_STEPS_PER_ROUND: usize = 8;

/// Cap on `numerator.bits() + denominator.bits()` of any candidate rational.
/// Past this the printed model would be bloated and further narrowing is
/// pointless — the search declines.
const MAX_CANDIDATE_BITS: u64 = 192;

/// Depth cap for the Stern-Brocot / continued-fraction walk. Each level
/// consumes one continued-fraction term of the answer, so genuine candidates
/// finish far below this; hitting it declines (fail closed).
const MAX_SIMPLEST_STEPS: usize = 200;

/// Refinement state for one algebraic model value: the exact point plus the
/// current isolating interval of the VALUE (not of the defining root when the
/// stored value is a residue expression — `to_number` already derived the
/// value's own defining data).
struct RefineVar {
    term: TermId,
    alpha: RealAlgebraic,
    lo: BigRational,
    hi: BigRational,
    /// Set when bisection certifies the value IS this rational.
    exact: Option<BigRational>,
}

/// Rollback data for one installed candidate assignment.
struct RefineTxn {
    /// Displaced LRA entries (`None` = key was absent).
    prev_lra: Vec<(TermId, Option<BigRational>)>,
    /// The model had no LRA component before installation.
    created_lra_model: bool,
}

/// `numerator.bits() + denominator.bits()` — the size guard for candidates.
fn rational_bits(r: &BigRational) -> u64 {
    r.numer().magnitude().bits() + r.denom().magnitude().bits()
}

/// The smallest-denominator rational STRICTLY between `lo` and `hi`
/// (Stern-Brocot / continued-fraction walk; among equal denominators the
/// smallest numerator magnitude). `None` when `lo >= hi` or the depth cap is
/// hit (fail closed).
fn simplest_rational_in_open(
    lo: &BigRational,
    hi: &BigRational,
    max_steps: usize,
) -> Option<BigRational> {
    if lo >= hi || max_steps == 0 {
        return None;
    }
    let zero = BigRational::zero();
    if *lo < zero && *hi > zero {
        return Some(zero);
    }
    if *hi <= zero {
        // Mirror the negative interval; simplicity is symmetric under
        // negation.
        return simplest_rational_in_open(&-hi.clone(), &-lo.clone(), max_steps - 1).map(|r| -r);
    }
    // 0 <= lo < hi.
    let f = lo.floor();
    let next_int = &f + BigRational::one();
    if next_int < *hi {
        // An integer lies strictly inside; it is the simplest possible.
        return Some(next_int);
    }
    // No integer strictly inside: x = f + 1/y maps (lo, hi) to the open
    // interval (1/(hi-f), 1/(lo-f)) for y (orientation flips; both ends stay
    // open), and simplicity of x is monotone in simplicity of y.
    let inv_lo = (hi - &f).recip();
    if *lo == f {
        // lo is exactly the integer f: y ranges over (inv_lo, +inf); the
        // simplest y is the next integer above inv_lo.
        let y = inv_lo.floor() + BigRational::one();
        return Some(f + y.recip());
    }
    let inv_hi = (lo - &f).recip();
    let y = simplest_rational_in_open(&inv_lo, &inv_hi, max_steps - 1)?;
    Some(f + y.recip())
}

/// One candidate rational per refined variable, or `None` when any candidate
/// is unavailable (interval degenerate, walk depth cap) or oversized
/// (`MAX_CANDIDATE_BITS`) — the caller then declines.
fn candidates(state: &[RefineVar]) -> Option<Vec<(TermId, BigRational)>> {
    let mut out = Vec::with_capacity(state.len());
    for v in state {
        let c = match &v.exact {
            Some(r) => r.clone(),
            None => simplest_rational_in_open(&v.lo, &v.hi, MAX_SIMPLEST_STEPS)?,
        };
        if rational_bits(&c) > MAX_CANDIDATE_BITS {
            return None;
        }
        out.push((v.term, c));
    }
    Some(out)
}

/// Narrow every interval by up to [`BISECT_STEPS_PER_ROUND`] exact bisection
/// steps against the algebraic value. Returns `false` when nothing narrowed
/// (every comparison declined) — the caller then stops: candidates would
/// repeat forever.
fn narrow(state: &mut [RefineVar]) -> bool {
    let two = BigRational::from_integer(BigInt::from(2));
    let mut progressed = false;
    for v in state.iter_mut() {
        if v.exact.is_some() {
            continue;
        }
        for _ in 0..BISECT_STEPS_PER_ROUND {
            let mid = (&v.lo + &v.hi) / &two;
            match v.alpha.cmp_rational(&mid) {
                Some(Ordering::Greater) => {
                    v.lo = mid;
                    progressed = true;
                }
                Some(Ordering::Less) => {
                    v.hi = mid;
                    progressed = true;
                }
                Some(Ordering::Equal) => {
                    // The value IS this rational; substitution is
                    // value-preserving.
                    v.exact = Some(mid);
                    progressed = true;
                    break;
                }
                // Exact comparison hit its internal refinement cap: stop
                // narrowing this value (fail closed; the driver's round cap
                // still bounds the whole search).
                None => break,
            }
        }
    }
    progressed
}

impl Executor {
    /// Apply the bounded, decline-only NRA refinement immediately before
    /// rendering. On decline the algebraic model remains bit-for-bit intact.
    pub(crate) fn model_after_nra_refinement(&mut self) -> String {
        self.refine_nra_algebraic_model_for_print();
        self.model()
    }

    /// Model-print-time rational refinement of algebraic NRA witnesses
    /// (#nra-rational-refinement). Bounded and DECLINE-ONLY: either the whole
    /// refined assignment exactly satisfies every assertion and becomes the
    /// model, or the model is left untouched. Runs at most once per SAT
    /// verdict.
    pub(crate) fn refine_nra_algebraic_model_for_print(&mut self) {
        if self.nra_algebraic_model.print_refinement_attempted() {
            return;
        }
        if !matches!(self.last_result, Some(SolveResult::Sat)) {
            return;
        }
        if self.nra_algebraic_model.is_empty() || self.last_model.is_none() {
            return;
        }
        self.nra_algebraic_model.mark_print_refinement_attempted();

        // Collect the irrational entries with the derived defining data of
        // each VALUE. Rational-valued residue entries already print as plain
        // rationals and need no refinement.
        let mut targets: Vec<(TermId, RealAlgebraic)> = Vec::new();
        for (&t, v) in self.nra_algebraic_model.iter() {
            match v.to_number_for_output() {
                Some(RealScalar::Rational(_)) => {}
                Some(RealScalar::Algebraic(n)) => targets.push((t, n.alpha().clone())),
                // No derived defining polynomial (refinement cap inside the
                // algebraic kernel): decline outright, keep today's output.
                None => return,
            }
        }
        if targets.is_empty() {
            return;
        }
        // Deterministic candidate order regardless of hash-map iteration.
        targets.sort_by_key(|(t, _)| t.0);

        let mut state: Vec<RefineVar> = targets
            .into_iter()
            .map(|(term, alpha)| {
                let (lo, hi) = {
                    let (l, h) = alpha.interval();
                    (l.clone(), h.clone())
                };
                RefineVar {
                    term,
                    alpha,
                    lo,
                    hi,
                    exact: None,
                }
            })
            .collect();

        // JOINT first (#nra-joint-refinement): when the algebraic value is
        // pinned by an equality coupling it to rational partners, moving it
        // ALONE can never satisfy that equality, and the per-value rounds
        // below would only narrow the intervals — leaving the joint pass with
        // huge candidate denominators. Run it on the fresh, wide intervals so
        // its chord slopes stay simple; on decline the model is untouched and
        // the per-value pass proceeds exactly as before.
        if self.refine_nra_joint(&mut state) {
            return;
        }

        let saved_nra = self.nra_algebraic_model.values().clone();
        let mut last_candidates: Option<Vec<(TermId, BigRational)>> = None;
        for round in 0..MAX_REFINE_ROUNDS {
            if round > 0 && !narrow(&mut state) {
                break;
            }
            let Some(cands) = candidates(&state) else {
                break;
            };
            if last_candidates.as_ref() == Some(&cands) {
                // Narrowing did not change any candidate; re-checking the
                // identical assignment is pointless.
                continue;
            }
            let Some(txn) = self.install_refined_candidates(&cands) else {
                break;
            };
            if self.refined_model_satisfies_all_assertions() {
                // Exact verification passed: the rational assignment IS the
                // model now (get-model and get-value both read it).
                return;
            }
            self.rollback_refined_candidates(&saved_nra, txn);
            last_candidates = Some(cands);
        }
        // Declined: the algebraic model is untouched.
    }

    /// Install a candidate assignment: drop the algebraic entries and place
    /// the rationals where the evaluator and the printers read Real values
    /// (the LRA model). Returns the rollback record.
    fn install_refined_candidates(&mut self, cands: &[(TermId, BigRational)]) -> Option<RefineTxn> {
        let model = self.last_model.as_mut()?;
        let created_lra_model = model.lra_model.is_none();
        let lra = model.lra_model.get_or_insert_with(|| LraModel {
            values: Default::default(),
        });
        let mut prev_lra = Vec::with_capacity(cands.len());
        for (t, r) in cands {
            self.nra_algebraic_model.remove(t);
            prev_lra.push((*t, lra.values.insert(*t, r.clone())));
        }
        Some(RefineTxn {
            prev_lra,
            created_lra_model,
        })
    }

    /// Undo [`Self::install_refined_candidates`] exactly.
    fn rollback_refined_candidates(
        &mut self,
        saved_nra: &DetHashMap<TermId, RealAlgebraicValue>,
        txn: RefineTxn,
    ) {
        self.nra_algebraic_model.replace_values(saved_nra.clone());
        let Some(model) = self.last_model.as_mut() else {
            return;
        };
        if txn.created_lra_model {
            model.lra_model = None;
            return;
        }
        if let Some(lra) = model.lra_model.as_mut() {
            for (t, prev) in txn.prev_lra {
                match prev {
                    Some(v) => {
                        lra.values.insert(t, v);
                    }
                    None => {
                        lra.values.remove(&t);
                    }
                }
            }
        }
    }

    /// STRICT exact re-check of the candidate model: every assertion must
    /// evaluate to `Bool(true)` under `evaluate_term` — the same exact
    /// evaluator model validation uses (pure BigRational arithmetic once all
    /// values are rational). `Unknown` or any non-true verdict declines; no
    /// SAT-fallback, no skips.
    ///
    /// The evaluation runs in an ISOLATED memo universe
    /// ([`super::with_isolated_eval_memo`]): the refinement loop mutates the
    /// model between candidate rechecks, so a value memoized under one
    /// candidate must never be read under another — and must never poison an
    /// ambient session some future caller might hold open across the
    /// `GetModel` dispatch.
    fn refined_model_satisfies_all_assertions(&self) -> bool {
        let Some(model) = self.last_model.as_ref() else {
            return false;
        };
        super::with_isolated_eval_memo(|| {
            self.ctx
                .assertions
                .iter()
                .all(|&a| matches!(self.evaluate_term(model, a), EvalValue::Bool(true)))
        })
    }
}

mod joint;

#[cfg(test)]
mod tests;
