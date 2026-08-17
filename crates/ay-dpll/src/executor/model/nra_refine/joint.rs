// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! JOINT rational refinement: move an equality-pinned algebraic witness
//! TOGETHER with the rational partners that pin it (#nra-joint-refinement).
//!
//! WHY (measured, the development design notes):
//! of the 218 mvnra-full models that carry a `root-obj` value, 150 are pinned
//! on a variety with NO rational point at all (`x² = 3`, the congruum curve,
//! the Fermat cubic — unvalidatable for every rationals-only validator), but
//! 68 are pinned on a variety whose rational points are DENSE (`s² + c² = 1`
//! and friends). The per-value pass in the parent module cannot reach those
//! 68: it moves only the algebraic value, and `skoS² + skoC² = 1` with
//! `skoS = 1/2` held fixed forces `skoC = ±√3/2`. The partners have to move
//! too.
//!
//! HOW. Everything here only PROPOSES a fully rational assignment; the parent
//! module's exact re-check of EVERY assertion
//! (`refined_model_satisfies_all_assertions`) is the sole acceptance
//! authority, and a declined proposal leaves the algebraic model bit-for-bit
//! intact. The structural analysis is therefore deliberately allowed to be
//! partial: a shape it misreads costs a wasted candidate, never a wrong model.
//!
//!   1. Collect the positive-polarity equalities (conjunctive positions only)
//!      and grow the equality cluster reachable from the algebraic variable.
//!   2. Greedily eliminate partners that occur AFFINELY in some equality: such
//!      a partner is solved exactly from that equality at every candidate
//!      point (`skoX := skoSX² − 1`), so its equality holds by construction.
//!   3. What is left is either
//!      * NOTHING — the FREE mode: pick the simplest rational near the
//!        algebraic value (exactly the parent module's candidate) and let the
//!        eliminated partners follow. This is the `s² = x ± 1`, `y³ = x`,
//!        `s² = x + y` family, where the partners absorb the move; or
//!      * ONE equality — the CHORD mode: with every other variable held at its
//!        model value, that equality is a curve in the two remaining unknowns
//!        (the algebraic value `u` and one partner `v`). Find one rational
//!        point `P` on it by fixing `v` at a simple rational and solving the
//!        resulting quadratic in `u` exactly (`exact_rational_sqrt`), then
//!        sweep chords through `P`: a line through a rational point of a conic
//!        meets it again in a RATIONAL point, for every rational slope. Slopes
//!        come from the exact isolating interval of the true chord slope, so
//!        the proposed points converge on the model point and eventually
//!        satisfy the instance's strict inequalities too.
//!
//! A fourth sample rejects every cubic but not every higher-degree restriction;
//! it is a candidate-budget filter, not proof of quadraticity. Every proposed
//! point must still pass an exact residual check and the whole-assertion gate.
//! Bounds: cluster size, partner choices, seed values, rounds and candidate
//! bit-width are all hard-capped, and the pass runs once per SAT verdict inside
//! the parent's one-shot guard.
//!
//! SORTS. Whole-model assertion evaluation is exact over rationals, but it does
//! not by itself enforce that an `Int`-sorted variable has an integral value.
//! Because the equality cluster intentionally admits both arithmetic sorts,
//! every proposal is checked against declared sorts before installation.

use ay_core::kani_compat::DetHashMap;
use ay_core::{Sort, TermId};
use num_rational::BigRational;
use num_traits::{One, Zero};

use self::math::{quadratic_fit, rat, rational_roots, seed_values};
use super::{narrow, rational_bits, simplest_rational_in_open, RefineVar, MAX_SIMPLEST_STEPS};
use crate::executor::model::{with_isolated_eval_memo, EvalValue};
use crate::executor::Executor;

mod math;
mod plan;

/// Cap on positive equalities harvested from the assertion set.
const MAX_EQUALITIES: usize = 64;

/// Cap on term-DAG nodes visited while harvesting equalities and while
/// collecting a term's variables (fail closed past it).
const MAX_SCAN_NODES: usize = 100_000;

/// Cap on the equality cluster reachable from the algebraic variable.
const MAX_CLUSTER_EQS: usize = 8;

/// Cap on distinct arithmetic variables in that cluster.
const MAX_CLUSTER_VARS: usize = 8;

/// Partners tried as the chord's second coordinate.
const MAX_PARTNER_CHOICES: usize = 4;

/// Candidate rounds per attempt; each round is one exact whole-model re-check.
const MAX_JOINT_ROUNDS: usize = 12;

/// `narrow` rounds spent separating the algebraic value from the seed point's
/// coordinate before the chord slope can be enclosed. The two are a rational
/// and an irrational, so separation is immediate in practice.
const MAX_SEPARATION_ROUNDS: usize = 8;

/// Cap on `numerator.bits() + denominator.bits()` of a proposed value. Higher
/// than the per-value pass's cap on purpose: a chord point carries the SQUARE
/// of the slope's denominator, and a solved partner squares it again, so the
/// per-value cap would decline points that are perfectly good models.
const MAX_JOINT_CANDIDATE_BITS: u64 = 512;

/// One positive-polarity equality plus the arithmetic variables it mentions.
struct Equality {
    lhs: TermId,
    rhs: TermId,
    vars: Vec<TermId>,
}

/// A partner variable determined by an equality that is affine in it.
struct Solve {
    var: TermId,
    eq: usize,
}

/// The elimination plan for one algebraic witness.
struct Plan {
    /// The algebraic variable being refined.
    alpha: TermId,
    /// Cluster equalities, in a deterministic order.
    eqs: Vec<Equality>,
    /// Partners solved exactly from an equality, in dependency order.
    solves: Vec<Solve>,
    /// Partners left free: they keep their model value unless chosen as the
    /// chord's second coordinate.
    free: Vec<TermId>,
    /// Model values of every cluster variable except the algebraic one.
    values: DetHashMap<TermId, BigRational>,
    /// The one equality left as a curve, if any (chord mode).
    residual: Option<usize>,
}

impl Executor {
    /// Attempt the joint refinement of the single algebraic witness in
    /// `state`. `true` means a fully rational assignment passed the parent's
    /// exact whole-model re-check and IS the model now; on `false` the
    /// algebraic model is untouched.
    pub(super) fn refine_nra_joint(&mut self, state: &mut [RefineVar]) -> bool {
        // One equality-pinned witness is the measured shape of all 68
        // refinable instances; several coupled algebraic values would need a
        // joint parametrization this pass does not implement (fail closed).
        if state.len() != 1 || state[0].exact.is_some() {
            return false;
        }
        let alpha = state[0].term;
        let Some(proxy) = simplest_rational_in_open(&state[0].lo, &state[0].hi, MAX_SIMPLEST_STEPS)
        else {
            return false;
        };
        let Some(equalities) = self.collect_positive_equalities() else {
            return false;
        };
        let Some(plan) = self.build_plan(alpha, equalities, &proxy) else {
            return false;
        };
        if plan.residual.is_none() {
            return self.joint_free_rounds(&plan, state);
        }
        // Chord points range over rationals. Do not spend the bounded partner
        // budget on an Int coordinate; the assignment-wide sort check below
        // remains the authority for solved and carried partners as well.
        let partners: Vec<TermId> = plan
            .free
            .iter()
            .copied()
            .filter(|term| !matches!(self.ctx.terms.sort(*term), Sort::Int))
            .take(MAX_PARTNER_CHOICES)
            .collect();
        for beta in partners {
            if self.joint_chord_rounds(&plan, state, beta) {
                return true;
            }
        }
        false
    }

    /// FREE mode: the algebraic value moves to the simplest nearby rational
    /// and every eliminated partner follows it exactly.
    fn joint_free_rounds(&mut self, plan: &Plan, state: &mut [RefineVar]) -> bool {
        if plan.solves.is_empty() {
            // Nothing here that the per-value pass does not already do.
            return false;
        }
        let mut last: Option<BigRational> = None;
        for round in 0..MAX_JOINT_ROUNDS {
            if round > 0 && !narrow(state) {
                return false;
            }
            let Some(a) = simplest_rational_in_open(&state[0].lo, &state[0].hi, MAX_SIMPLEST_STEPS)
            else {
                return false;
            };
            if last.as_ref() == Some(&a) {
                continue;
            }
            last = Some(a.clone());
            if self.try_joint_assignment(plan, None, &a, None) {
                return true;
            }
        }
        false
    }

    /// CHORD mode: sweep rational chords of the residual curve through a
    /// rational point of it, with slopes drawn from the exact enclosure of the
    /// true chord slope so the points converge on the model point.
    fn joint_chord_rounds(&mut self, plan: &Plan, state: &mut [RefineVar], beta: TermId) -> bool {
        let Some(beta_value) = plan.values.get(&beta).cloned() else {
            return false;
        };
        let Some((seed_u, seed_v)) = self.seed_point(plan, beta) else {
            return false;
        };
        // Chord slope `(β̄ − v₀) / (ᾱ − u₀)`. A zero numerator would put the
        // model point on the horizontal line through the seed, which on a
        // genuine conic forces the model point to be rational as well.
        let numerator = &beta_value - &seed_v;
        if numerator.is_zero() {
            return false;
        }
        // The denominator's enclosure must exclude 0: `ᾱ` is irrational and
        // `u₀` rational, so bisection always separates them.
        for _ in 0..MAX_SEPARATION_ROUNDS {
            if state[0].lo > seed_u || state[0].hi < seed_u {
                break;
            }
            if !narrow(state) {
                return false;
            }
        }
        if state[0].lo <= seed_u && state[0].hi >= seed_u {
            return false;
        }
        let mut last: Option<BigRational> = None;
        for round in 0..MAX_JOINT_ROUNDS {
            if round > 0 && !narrow(state) {
                return false;
            }
            let d_lo = &state[0].lo - &seed_u;
            let d_hi = &state[0].hi - &seed_u;
            if d_lo.is_zero() || d_hi.is_zero() {
                return false;
            }
            let (mut t_lo, mut t_hi) = (&numerator / &d_lo, &numerator / &d_hi);
            if t_lo > t_hi {
                std::mem::swap(&mut t_lo, &mut t_hi);
            }
            let Some(t) = simplest_rational_in_open(&t_lo, &t_hi, MAX_SIMPLEST_STEPS) else {
                continue;
            };
            if last.as_ref() == Some(&t) {
                continue;
            }
            last = Some(t.clone());
            let Some((a, b)) = self.chord_second_point(plan, beta, &seed_u, &seed_v, &t) else {
                continue;
            };
            if self.try_joint_assignment(plan, Some(beta), &a, Some(&b)) {
                return true;
            }
        }
        false
    }

    /// The second intersection of the residual curve with the line of slope
    /// `t` through the seed point — rational whenever that restriction is a
    /// genuine quadratic, which is confirmed exactly here, never assumed.
    fn chord_second_point(
        &mut self,
        plan: &Plan,
        beta: TermId,
        seed_u: &BigRational,
        seed_v: &BigRational,
        t: &BigRational,
    ) -> Option<(BigRational, BigRational)> {
        let point = |lambda: i64| {
            let l = rat(lambda);
            (seed_u + &l, seed_v + t * &l)
        };
        let (u1, v1) = point(1);
        let (um1, vm1) = point(-1);
        let (u2, v2) = point(2);
        let at0 = self.residual_at(plan, Some(beta), seed_u, Some(seed_v))?;
        let at1 = self.residual_at(plan, Some(beta), &u1, Some(&v1))?;
        let at_m1 = self.residual_at(plan, Some(beta), &um1, Some(&vm1))?;
        let at2 = self.residual_at(plan, Some(beta), &u2, Some(&v2))?;
        let (c0, c1, c2) = quadratic_fit(&at0, &at1, &at_m1, &at2)?;
        // The seed must be ON the curve, and the line must meet it twice.
        if !c0.is_zero() || c2.is_zero() {
            return None;
        }
        let lambda = -c1 / c2;
        if lambda.is_zero() {
            return None;
        }
        Some((seed_u + &lambda, seed_v + t * &lambda))
    }

    /// A rational point on the residual curve: fix ONE coordinate at a simple
    /// rational and solve the resulting quadratic in the other exactly. Both
    /// directions are tried — `s² = (1+a²)(1+b²)` with `a = 1/2` has the
    /// rational point `(b, s) = (1/2, 5/4)`, reachable by fixing `b` but not
    /// by fixing `s` at any simple value. Every returned point is confirmed by
    /// an exact residual evaluation.
    fn seed_point(&mut self, plan: &Plan, beta: TermId) -> Option<(BigRational, BigRational)> {
        let model_values: Vec<BigRational> = plan.values.values().cloned().collect();
        for value in seed_values(&model_values) {
            for fix_partner in [true, false] {
                if let Some(point) = self.seed_along(plan, beta, &value, fix_partner) {
                    return Some(point);
                }
            }
        }
        None
    }

    /// One direction of the seed search: hold the partner coordinate (or the
    /// algebraic one) at `fixed` and solve the residual's quadratic in the
    /// other coordinate.
    fn seed_along(
        &mut self,
        plan: &Plan,
        beta: TermId,
        fixed: &BigRational,
        fix_partner: bool,
    ) -> Option<(BigRational, BigRational)> {
        let coords = |free: BigRational| -> (BigRational, BigRational) {
            if fix_partner {
                (free, fixed.clone())
            } else {
                (fixed.clone(), free)
            }
        };
        let samples = [
            BigRational::zero(),
            BigRational::one(),
            -BigRational::one(),
            rat(2),
        ];
        let mut at = Vec::with_capacity(samples.len());
        for sample in samples {
            let (u, v) = coords(sample);
            at.push(self.residual_at(plan, Some(beta), &u, Some(&v))?);
        }
        let (c0, c1, c2) = quadratic_fit(&at[0], &at[1], &at[2], &at[3])?;
        for root in rational_roots(&c0, &c1, &c2) {
            if rational_bits(&root) > MAX_JOINT_CANDIDATE_BITS {
                continue;
            }
            let (u, v) = coords(root);
            match self.residual_at(plan, Some(beta), &u, Some(&v)) {
                Some(residual) if residual.is_zero() => return Some((u, v)),
                _ => {}
            }
        }
        None
    }

    /// Install a proposed joint assignment and submit it to the parent's exact
    /// whole-model gate. Rolls back on any decline.
    fn try_joint_assignment(
        &mut self,
        plan: &Plan,
        beta: Option<TermId>,
        a: &BigRational,
        b: Option<&BigRational>,
    ) -> bool {
        let Some(assignment) = self.chain_assignment(plan, beta, a, b) else {
            return false;
        };
        if !self.assignment_respects_sorts(&assignment) {
            return false;
        }
        if assignment
            .iter()
            .any(|(_, value)| rational_bits(value) > MAX_JOINT_CANDIDATE_BITS)
        {
            return false;
        }
        if let Some(index) = plan.residual {
            // Cheap pre-check: a candidate that does not even satisfy the
            // curve it was drawn from cannot satisfy the assertion set.
            match self.probe_residual(&assignment, &plan.eqs[index]) {
                Some(residual) if residual.is_zero() => {}
                _ => return false,
            }
        }
        let saved = self.nra_algebraic_model.values().clone();
        let Some(txn) = self.install_refined_candidates(&assignment) else {
            return false;
        };
        if self.refined_model_satisfies_all_assertions() {
            return true;
        }
        self.rollback_refined_candidates(&saved, txn);
        false
    }

    /// The residual of the plan's remaining equality at `(α := a, β := b)`,
    /// with every eliminated partner solved and every other partner held at
    /// its model value.
    fn residual_at(
        &mut self,
        plan: &Plan,
        beta: Option<TermId>,
        a: &BigRational,
        b: Option<&BigRational>,
    ) -> Option<BigRational> {
        let index = plan.residual?;
        let assignment = self.chain_assignment(plan, beta, a, b)?;
        self.probe_residual(&assignment, &plan.eqs[index])
    }

    /// The full rational assignment implied by `(α := a, β := b)`: the free
    /// partners at their model values, then every eliminated partner solved
    /// exactly from its equality, in dependency order.
    fn chain_assignment(
        &mut self,
        plan: &Plan,
        beta: Option<TermId>,
        a: &BigRational,
        b: Option<&BigRational>,
    ) -> Option<Vec<(TermId, BigRational)>> {
        let mut assignment: Vec<(TermId, BigRational)> = vec![(plan.alpha, a.clone())];
        for free in &plan.free {
            if Some(*free) == beta {
                assignment.push((*free, b?.clone()));
            } else {
                assignment.push((*free, plan.values.get(free)?.clone()));
            }
        }
        for solve in &plan.solves {
            let value = self.solve_affine(&assignment, solve.var, &plan.eqs[solve.eq])?;
            assignment.push((solve.var, value));
        }
        Some(assignment)
    }

    /// The exact solution of `eq` for `var`, given values for everything else
    /// it mentions. Affineness is CONFIRMED at three sample points; a
    /// non-affine occurrence (or a vanishing slope) declines.
    fn solve_affine(
        &mut self,
        assignment: &[(TermId, BigRational)],
        var: TermId,
        eq: &Equality,
    ) -> Option<BigRational> {
        let at0 = self.residual_with(assignment, var, &BigRational::zero(), eq)?;
        let at1 = self.residual_with(assignment, var, &BigRational::one(), eq)?;
        let at2 = self.residual_with(assignment, var, &rat(2), eq)?;
        let slope = &at1 - &at0;
        if slope.is_zero() || &at2 - &at1 != slope {
            return None;
        }
        Some(-at0 / slope)
    }

    /// `eq`'s residual with `var` pinned at `value` on top of `assignment`.
    fn residual_with(
        &mut self,
        assignment: &[(TermId, BigRational)],
        var: TermId,
        value: &BigRational,
        eq: &Equality,
    ) -> Option<BigRational> {
        let mut extended = assignment.to_vec();
        extended.push((var, value.clone()));
        self.probe_residual(&extended, eq)
    }

    /// ONE exact evaluation of `lhs − rhs` under a fully rational trial
    /// assignment, through the SAME model evaluator the acceptance gate uses.
    /// The assignment is installed and rolled back around the evaluation, and
    /// the evaluation runs in an isolated memo universe — every probe is a
    /// different assignment, so a memoized value must never leak across them.
    fn probe_residual(
        &mut self,
        assignment: &[(TermId, BigRational)],
        eq: &Equality,
    ) -> Option<BigRational> {
        let saved = self.nra_algebraic_model.values().clone();
        let txn = self.install_refined_candidates(assignment)?;
        let value = match self.last_model.as_ref() {
            None => None,
            Some(model) => with_isolated_eval_memo(|| {
                match (
                    self.evaluate_term(model, eq.lhs),
                    self.evaluate_term(model, eq.rhs),
                ) {
                    (EvalValue::Rational(lhs), EvalValue::Rational(rhs)) => Some(lhs - rhs),
                    _ => None,
                }
            }),
        };
        self.rollback_refined_candidates(&saved, txn);
        value
    }
}

#[cfg(test)]
mod tests;
