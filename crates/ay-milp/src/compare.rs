// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! THE COMPARISON KERNEL: when do two answers to the same model contradict?
//!
//! # Why equality is the wrong test, measured
//!
//! Every A/B in this repo compares two runs of the same model, and the obvious
//! oracle is "the verdicts must be identical". An earlier draft of
//! the development design notes mandated exactly that
//! for every `class: Economics` kill-switch fixture.
//!
//! It is wrong on most of the corpus. the development design notes holds 850 arm-instance
//! cells, and **500 of them (59%) are `FEASIBLE`** — an incumbent at a deadline. Two
//! runs that stop at different points in the same search legitimately hold different
//! incumbents, so an equality oracle fires on the majority of instances and reports
//! a contradiction that is not one. An oracle that cries wolf on 59% of cells gets
//! deleted, and then the real contradictions go unreported with it.
//!
//! # The information order
//!
//! An outcome is a set of CLAIMS about the same underlying optimum. Two outcomes
//! contradict only when no single answer satisfies both:
//!
//! ```text
//!             Optimal{v}          Infeasible
//!                 |                    |
//!          Feasible{v, dual}           |
//!                 |                    |
//!             Bound{b}                 |
//!                 \                   /
//!                      Unknown
//! ```
//!
//! `Unknown` is the bottom: it claims nothing and contradicts nothing, which is why
//! contention is safe here (see [`Verdict`]). `Optimal` and `Infeasible` are maximal
//! and mutually exclusive. Everything else constrains a range.
//!
//! # Two gates the naive version misses
//!
//! * **A non-rigorous bound may never exclude a point.** `outcome.rs` states it:
//!   *"Callers must not use a non-rigorous bound to exclude feasible points."* A
//!   comparison kernel that forgets this manufactures contradictions out of float
//!   advice, which is precisely the class of wrong answer this engine exists not to
//!   produce.
//! * **`Feasible { incumbent_only }` is not a claim of optimality.** An incumbent
//!   that is worse than another run's proven optimum is expected, not a conflict.
//!
//! # Contention asymmetry
//!
//! Every relation here is monotone in the information order, and contention can only
//! move an outcome DOWN it — a slower box proves less, never more. So for an
//! INVERTED test (green = still refuted, the shape `P4`'s refutation ledger needs) a
//! contended box yields false GREEN, never false RED. That is the right direction to
//! fail: a missed finding costs a re-run, a false alarm costs trust.

use num_rational::BigRational;

use crate::model::Sense;
use crate::outcome::Outcome;

/// What two outcomes for the same model say about each other.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    /// No single answer satisfies both. One of the two runs is wrong.
    Contradiction {
        /// What the conflict is, in words an operator can act on.
        detail: String,
    },
    /// Both hold, and `a` is at least as informative as `b`.
    AIsStronger,
    /// Both hold, and `b` is at least as informative as `a`.
    BIsStronger,
    /// Both hold and neither dominates — e.g. two incumbents from interrupted runs.
    Compatible,
}

impl Verdict {
    /// The only question most callers have.
    #[must_use]
    pub fn is_contradiction(&self) -> bool {
        matches!(self, Verdict::Contradiction { .. })
    }
}

/// Is `lhs` strictly better than `rhs` in `sense`?
fn better(sense: Sense, lhs: &BigRational, rhs: &BigRational) -> bool {
    match sense {
        Sense::Minimize => lhs < rhs,
        Sense::Maximize => lhs > rhs,
    }
}

/// The objective value an outcome asserts is ACHIEVABLE, if it asserts one.
///
/// `Feasible` carries a point, so its value is achievable whether or not the run was
/// interrupted; `incumbent_only` bears on optimality, not on attainment.
fn attained(o: &Outcome, obj: impl Fn(&[BigRational]) -> BigRational) -> Option<BigRational> {
    match o {
        Outcome::Optimal { value, .. } => Some(value.clone()),
        Outcome::Feasible { model_values, .. } => Some(obj(model_values)),
        _ => None,
    }
}

/// The bound an outcome asserts NOTHING CAN BEAT, if it asserts one and that
/// assertion is rigorous.
///
/// `Bound { rigorous: false }` deliberately yields `None`: float advice may not
/// exclude a point.
fn excludes_beyond(o: &Outcome) -> Option<BigRational> {
    match o {
        Outcome::Optimal { value, .. } => Some(value.clone()),
        Outcome::Feasible {
            dual_bound: Some(b),
            ..
        } => Some(b.clone()),
        Outcome::Bound {
            dual_bound,
            rigorous: true,
        } => Some(dual_bound.clone()),
        _ => None,
    }
}

/// How informative an outcome is, for the dominance answer. Higher is stronger.
fn rank(o: &Outcome) -> u8 {
    match o {
        Outcome::Unknown { .. } => 0,
        Outcome::Bound { .. } => 1,
        Outcome::Feasible { .. } => 2,
        Outcome::Optimal { .. } | Outcome::Infeasible { .. } | Outcome::Unbounded => 3,
    }
}

/// Compare two outcomes for the same model under `sense`.
///
/// `objective` evaluates a point, so the kernel can compare a `Feasible` incumbent
/// against another run's proven optimum without trusting either run's own arithmetic.
///
/// # The contradictions detected
///
/// 1. two `Optimal` values differ;
/// 2. an `Optimal` coexists with a strictly better attained point;
/// 3. an `Infeasible` coexists with any attained point;
/// 4. a rigorous bound excludes a point the other run actually attained;
/// 5. `Unbounded` coexists with a proven finite optimum.
pub fn compare(
    a: &Outcome,
    b: &Outcome,
    sense: Sense,
    objective: impl Fn(&[BigRational]) -> BigRational + Copy,
) -> Verdict {
    let contradiction = |detail: String| Verdict::Contradiction { detail };

    // (1) Two proven optima must agree.
    if let (Outcome::Optimal { value: va, .. }, Outcome::Optimal { value: vb, .. }) = (a, b) {
        if va != vb {
            return contradiction(format!(
                "both runs proved optimality and disagree: {va} vs {vb}"
            ));
        }
    }

    // (5) Unboundedness versus a finite proof.
    for (u, o) in [(a, b), (b, a)] {
        if matches!(u, Outcome::Unbounded) {
            if let Outcome::Optimal { value, .. } = o {
                return contradiction(format!(
                    "one run reports the objective unbounded, the other proved the finite \
                     optimum {value}"
                ));
            }
        }
    }

    let (av, bv) = (attained(a, objective), attained(b, objective));

    // (3) Infeasibility versus an attained point. The point is `check_point`-verified
    //     at the rim, so this is the sharpest contradiction the kernel can report.
    for (inf, pt) in [(a, &bv), (b, &av)] {
        if matches!(inf, Outcome::Infeasible { .. }) {
            if let Some(v) = pt {
                return contradiction(format!(
                    "one run proved infeasibility, the other attained a feasible point \
                     valued {v}"
                ));
            }
        }
    }

    // (2) and (4): a claim that nothing beats `bound`, against a point that does.
    //     `incumbent_only` does not matter here — attainment is attainment.
    for (claimant, point) in [(a, &bv), (b, &av)] {
        if let (Some(bound), Some(v)) = (excludes_beyond(claimant), point) {
            if better(sense, v, &bound) {
                return contradiction(format!(
                    "one run claims nothing beats {bound}, the other attained {v}, which is \
                     better under {sense:?}"
                ));
            }
        }
    }

    match rank(a).cmp(&rank(b)) {
        std::cmp::Ordering::Greater => Verdict::AIsStronger,
        std::cmp::Ordering::Less => Verdict::BIsStronger,
        std::cmp::Ordering::Equal => Verdict::Compatible,
    }
}

// ------------------------------------------------------ trajectory classifier

/// Whether two arms of a gate walked the SAME search, or different ones.
///
/// # Why this is worth having, and why only here
///
/// If a gate's two arms visit the same nodes and spend the same simplex iterations
/// per phase, the gate cannot have changed which answer is reachable — it is a
/// **pure cost change**, and it needs only a paired timing test rather than a
/// verdict comparison across the corpus. That collapses the fixture burden for a
/// large fraction of the 64 kill switches.
///
/// This is cheap because AY keeps a byte-identical arm for every shipped
/// optimisation. `--ft-spike` is the live example — `knobs.rs` records that
/// *"Both arms leave BYTE-IDENTICAL engine state"* — so the classifier has a known
/// positive to validate against. No configurator can do this, because none of them
/// has an arm that restores prior behaviour exactly.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Trajectory {
    /// Same nodes, same per-phase iteration vector: a pure cost change.
    Identical,
    /// The arms diverged; the gate moved the search and needs a full comparison.
    Diverged {
        /// First phase index whose iteration count differs, if the divergence is
        /// in the phase vector rather than the node count.
        first_phase: Option<usize>,
    },
}

/// Classify a gate from two arms' `(nodes, per-phase iterations)` traces.
///
/// The phase vector is `simplex`'s 12-phase ledger. Counts only — deliberately no
/// wall clock, so the classification reproduces on a contended box.
#[must_use]
pub fn classify(a: (u64, &[u64]), b: (u64, &[u64])) -> Trajectory {
    let ((a_nodes, a_ph), (b_nodes, b_ph)) = (a, b);
    if a_nodes != b_nodes || a_ph.len() != b_ph.len() {
        return Trajectory::Diverged { first_phase: None };
    }
    match a_ph.iter().zip(b_ph).position(|(x, y)| x != y) {
        Some(i) => Trajectory::Diverged {
            first_phase: Some(i),
        },
        None => Trajectory::Identical,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::Zero;

    fn r(n: i64) -> BigRational {
        BigRational::from_integer(n.into())
    }

    /// The point's value is whatever the caller's objective says — the kernel never
    /// trusts a run's own arithmetic about the other run's point.
    fn obj(p: &[BigRational]) -> BigRational {
        p.first().cloned().unwrap_or_else(BigRational::zero)
    }

    fn optimal(v: i64) -> Outcome {
        Outcome::Optimal {
            value: r(v),
            model_values: vec![r(v)],
            cert: None,
        }
    }
    fn feasible(v: i64, dual: Option<i64>) -> Outcome {
        Outcome::Feasible {
            model_values: vec![r(v)],
            incumbent_only: true,
            dual_bound: dual.map(r),
        }
    }

    /// THE MEASURED REASON THIS KERNEL EXISTS. 500 of 850 cells in pf-30s.json are
    /// FEASIBLE at a deadline, so an equality oracle fires on 59% of the corpus. Two
    /// different incumbents are compatible, not a contradiction.
    #[test]
    fn two_different_incumbents_are_not_a_contradiction() {
        let v = compare(
            &feasible(10, None),
            &feasible(7, None),
            Sense::Minimize,
            obj,
        );
        assert!(
            !v.is_contradiction(),
            "an equality oracle would fire here, on 59% of the corpus: {v:?}"
        );
    }

    /// An interrupted run holding a worse incumbent than another run's proven
    /// optimum is the normal case, not a conflict.
    #[test]
    fn a_worse_incumbent_than_a_proven_optimum_is_compatible() {
        assert!(!compare(&optimal(5), &feasible(9, None), Sense::Minimize, obj).is_contradiction());
        // ... but a BETTER point than a proven optimum is a real contradiction.
        assert!(compare(&optimal(5), &feasible(3, None), Sense::Minimize, obj).is_contradiction());
    }

    #[test]
    fn two_proven_optima_must_agree() {
        assert!(compare(&optimal(5), &optimal(6), Sense::Minimize, obj).is_contradiction());
        assert!(!compare(&optimal(5), &optimal(5), Sense::Minimize, obj).is_contradiction());
    }

    #[test]
    fn infeasible_against_any_attained_point_is_the_sharpest_contradiction() {
        let inf = Outcome::Infeasible {
            cert: None,
            tree_cert: None,
        };
        assert!(compare(&inf, &feasible(1, None), Sense::Minimize, obj).is_contradiction());
        assert!(compare(&inf, &optimal(1), Sense::Minimize, obj).is_contradiction());
    }

    /// A NON-RIGOROUS BOUND MAY NEVER EXCLUDE A POINT. Forgetting this manufactures
    /// contradictions out of float advice — the exact class of wrong answer this
    /// engine exists not to produce.
    #[test]
    fn a_non_rigorous_bound_cannot_contradict_anything() {
        let loose = Outcome::Bound {
            dual_bound: r(100),
            rigorous: false,
        };
        // A point at 1 is far "better" than a claimed floor of 100 under Minimize.
        assert!(
            !compare(&loose, &feasible(1, None), Sense::Minimize, obj).is_contradiction(),
            "float advice must never be used to exclude a feasible point"
        );
        // The same bound, marked rigorous, IS a contradiction.
        let tight = Outcome::Bound {
            dual_bound: r(100),
            rigorous: true,
        };
        assert!(compare(&tight, &feasible(1, None), Sense::Minimize, obj).is_contradiction());
    }

    /// The tree's own dual bound on an interrupted run is rigorous, so it can
    /// contradict — but only in the direction that excludes an attained point.
    #[test]
    fn an_interrupted_runs_dual_bound_still_excludes() {
        assert!(
            compare(
                &feasible(9, Some(8)),
                &feasible(3, None),
                Sense::Minimize,
                obj
            )
            .is_contradiction(),
            "a rigorous floor of 8 cannot coexist with an attained 3"
        );
    }

    /// Sense is honoured: what is better flips.
    #[test]
    fn maximize_flips_which_side_is_better() {
        assert!(compare(&optimal(5), &feasible(9, None), Sense::Maximize, obj).is_contradiction());
        assert!(!compare(&optimal(5), &feasible(3, None), Sense::Maximize, obj).is_contradiction());
    }

    /// Unknown is the bottom of the order: it claims nothing, so it contradicts
    /// nothing. This is what makes contention safe — a slower box proves less, never
    /// more, so an inverted test yields false GREEN and never false RED.
    #[test]
    fn unknown_contradicts_nothing_and_is_dominated_by_everything() {
        let unk = Outcome::Unknown {
            reason: crate::outcome::UnknownReason::Timeout,
        };
        for other in [optimal(5), feasible(1, Some(0))] {
            let v = compare(&unk, &other, Sense::Minimize, obj);
            assert!(!v.is_contradiction());
            assert_eq!(v, Verdict::BIsStronger);
        }
    }

    #[test]
    fn identical_traces_classify_as_a_pure_cost_change() {
        let ph = [1u64, 2, 3];
        assert_eq!(classify((10, &ph), (10, &ph)), Trajectory::Identical);
        assert_eq!(
            classify((10, &ph), (11, &ph)),
            Trajectory::Diverged { first_phase: None },
            "a node-count difference is a divergence with no single phase to blame"
        );
        assert_eq!(
            classify((10, &[1, 2, 3]), (10, &[1, 9, 3])),
            Trajectory::Diverged {
                first_phase: Some(1)
            }
        );
    }
}
