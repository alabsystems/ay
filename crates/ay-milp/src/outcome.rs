// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solve outcomes.

use num_rational::BigRational;

use crate::cert::{FarkasCertificate, OptimalityCertificate};
use crate::tree_cert::MilpInfeasibilityCertificate;

/// Why a solve could not produce a verdict.
///
/// Anything the engine cannot warrant is `Unknown { reason }`; the API does
/// not encode an unsupported or interrupted solve as a definitive verdict.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum UnknownReason {
    /// The deadline or time limit expired.
    Timeout,
    /// The caller's interrupt fired.
    Interrupted,
    /// An internal iteration/node budget was exhausted without a proof.
    IterationLimit,
    /// A memory budget was exhausted.
    MemoryLimit,
    /// `require_certificates` was set and the verdict's certificate could
    /// not be produced.
    CertificateUnavailable,
    /// The underlying solver answered `unknown` for its own reasons.
    SolverIncomplete {
        /// The solver's stated reason, when available.
        detail: String,
    },
    /// A verdict's own witness failed independent re-validation against the
    /// model, so the verdict was withheld rather than returned.
    ///
    /// This never fires on a correct solver: it means a lane produced an
    /// infeasible primal point, a value its point does not attain, or a dual
    /// bound that contradicts its own primal. Emitting `Unknown` keeps the
    /// wrong answer off the API (contract property 1) and leaves the bug
    /// loud rather than silent.
    WitnessRejected {
        /// What failed re-validation.
        detail: String,
    },
}

/// The result of a solve.
///
/// Verdict-bearing variants carry their evidence (contract property 2:
/// "evidence is data"). Model-value vectors are indexed by column insertion
/// order, exact `BigRational` end-to-end.
#[derive(Debug, Clone)]
#[non_exhaustive]
#[must_use]
pub enum Outcome {
    /// A proven optimum. `model_values` is a feasible point achieving
    /// `value`; `cert` (when present) is the independently checkable dual
    /// bound completing the optimality proof.
    Optimal {
        /// The optimal objective value (including the model's offset).
        value: BigRational,
        /// A feasible point achieving `value`.
        model_values: Vec<BigRational>,
        /// Dual-bound evidence, when the certificate lane could produce it.
        cert: Option<OptimalityCertificate>,
    },
    /// A feasible point without an optimality claim.
    Feasible {
        /// The feasible point.
        model_values: Vec<BigRational>,
        /// True when the point is an incumbent from an interrupted
        /// optimization (a better point may exist).
        incumbent_only: bool,
        /// A rigorous dual bound on the optimum from the interrupted tree —
        /// the weakest Neumaier–Shcherbina/exact bound among the open
        /// subproblems and the incumbent, in the model's frame (lower bound
        /// for Minimize, upper for Maximize, offset included). `None` when
        /// any part of the tree was discarded without proof. Unlike an
        /// exported certificate, this bound is not independently checkable.
        dual_bound: Option<BigRational>,
    },
    /// Proven infeasible. `cert` (when present) is the exact root-LP Farkas
    /// witness — the PREFERRED evidence when available (one combination to
    /// check instead of a tree). `tree_cert` is the whole-tree case-split
    /// witness for infeasibility the relaxation alone cannot see. When both
    /// are absent the verdict rests on the exact solver without exported
    /// evidence.
    Infeasible {
        /// Exact root-LP infeasibility evidence, when available. Preferred
        /// over `tree_cert` when present.
        cert: Option<FarkasCertificate>,
        /// Whole-tree case-split evidence, when branch-and-bound could capture
        /// and re-derive its tree in the caller's model frame.
        tree_cert: Option<MilpInfeasibilityCertificate>,
    },
    /// The objective is unbounded in its optimization direction.
    Unbounded,
    /// A rigorous or heuristic dual bound without a full proof (native
    /// engine; interior nodes). `rigorous` is only set for
    /// Neumaier–Shcherbina-corrected or exact bounds.
    Bound {
        /// The dual bound (lower bound for Minimize, upper for Maximize).
        dual_bound: BigRational,
        /// Whether the bound is rigorous (directed-rounding-corrected or
        /// exact). Callers must not use a non-rigorous bound to exclude
        /// feasible points.
        rigorous: bool,
    },
    /// No verdict. NEVER a silent wrong value.
    Unknown {
        /// Why.
        reason: UnknownReason,
    },
}

/// How much of an [`Outcome`] rests on independently checkable evidence.
///
/// # Why a consumer needs this
///
/// the development design notes §M2 asks for a soundness class per
/// heuristic, and justifies tolerating "economics-only" settings freely with this
/// sentence (`:152`):
///
/// > *every verdict still rests on ay's exact certificates and `check_point`
/// > (fail-closed), so the recipe can change speed, never an answer.*
///
/// **That is not true for every outcome shape, and the exception is the shape the downstream optimization consumer's
/// own workload produces.** `LpSession::verify` asserts `bound == value` only when
/// `!model.has_integrality()` (`session.rs`); on an integral model the certificate
/// is checked for NON-CROSSING and nothing more. Measured against the corpus
/// snapshot in the development design notes: all 133 instances carry `ints > 0`, so **276
/// of 276 `OPTIMAL` verdicts in that dataset are search-trusted, not rim-closed.**
///
/// That is not a bug — a dual bound may legitimately trail a primal across an
/// integrality gap, and closing the gap is what the *search* does. It is a
/// statement about what the exported artifact proves, which a consumer pricing a
/// wrong verdict at −150 needs to be able to read off the API rather than infer
/// from the source.
///
/// # This is a method, not a field
///
/// A `trust:` field would be semver-breaking across every `Outcome::X { .. }`
/// construction site in the crate, would force a `Default`, and would then ship a
/// default tag on any exit that forgot to derive one. A wrong tag is worse than no
/// tag. A method is derived at the call site, cannot go stale, and covers **both**
/// exits — including `LpSession::rigorous_bound`, which builds
/// `Outcome::Bound { rigorous: true }` inline and never calls `finish`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Trust {
    /// Every claim this outcome makes was re-derived, against *this* model, from
    /// an artifact a third party could check.
    RimClosed,
    /// At least one claim rests on the engine's search or arithmetic being
    /// correct, with no exportable evidence for it. `why` names which.
    SearchTrusted {
        /// The specific claim that is not rim-closed.
        why: &'static str,
    },
}

impl Trust {
    /// True when a third party could re-check every claim from exported evidence.
    #[must_use]
    pub fn is_rim_closed(self) -> bool {
        matches!(self, Trust::RimClosed)
    }
}

impl Outcome {
    /// What in this outcome is backed by checkable evidence, and what is not.
    ///
    /// See [`Trust`] — in particular, an `Optimal` on an **integral** model is
    /// `SearchTrusted` even with a certificate present, because the certificate is
    /// only checked for non-crossing there.
    #[must_use]
    pub fn trust(&self, model: &crate::model::Model) -> Trust {
        // A model whose coefficients are not exactly representable is handled by
        // the session's fail-closed path before it can produce a verdict, but a
        // caller holding an `Outcome` cannot see that happened. Say so.
        if model.has_inexact_coeffs() {
            return Trust::SearchTrusted {
                why: "the model carries coefficients that are not exactly representable in f64; \
                      the exact rim reads them from the model's rational side, so the evidence \
                      is only as good as that transcription",
            };
        }
        match self {
            Self::Optimal { cert: None, .. } => Trust::SearchTrusted {
                why: "optimality with no exported dual bound: the value is the search's claim",
            },
            Self::Optimal { cert: Some(_), .. } => {
                if model.has_integrality() {
                    Trust::SearchTrusted {
                        why: "on an integral model the optimality certificate is checked for \
                              NON-CROSSING, not for meeting the primal; the integrality gap is \
                              closed by the search's exhaustiveness, which is not certified",
                    }
                } else {
                    Trust::RimClosed
                }
            }
            // `check_point` verifies the point against this model, and that is the
            // whole of the claim: `Feasible` asserts a point exists, not a bound.
            Self::Feasible {
                dual_bound: None, ..
            } => Trust::RimClosed,
            Self::Feasible {
                dual_bound: Some(_),
                ..
            } => Trust::SearchTrusted {
                why: "the point is rim-verified but the accompanying dual bound is the \
                      interrupted tree's own weakest open bound, which is not independently \
                      checkable (see `Outcome::Feasible::dual_bound`)",
            },
            Self::Infeasible {
                cert: Some(_) | None,
                tree_cert: Some(_),
            }
            | Self::Infeasible {
                cert: Some(_),
                tree_cert: None,
            } => Trust::RimClosed,
            Self::Infeasible {
                cert: None,
                tree_cert: None,
            } => Trust::SearchTrusted {
                why: "infeasibility with neither a Farkas witness nor a tree certificate: the \
                      verdict rests on the exact solver without exported evidence",
            },
            Self::Bound { rigorous: true, .. } => Trust::SearchTrusted {
                why: "a rigorous (Neumaier-Shcherbina-corrected or exact) bound is SOUND but is \
                      not an exported artifact, and `LpSession::rigorous_bound` returns one \
                      without passing through the certificate policy at all",
            },
            Self::Bound {
                rigorous: false, ..
            } => Trust::SearchTrusted {
                why: "a non-rigorous bound; it must never be used to exclude a feasible point",
            },
            Self::Unbounded => Trust::SearchTrusted {
                why: "unboundedness is reported without an exported ray",
            },
            // No claim is made, so there is nothing to back — but `RimClosed`
            // would read as an endorsement.
            Self::Unknown { .. } => Trust::SearchTrusted { why: "no verdict" },
        }
    }

    /// True for `Optimal` / `Feasible`.
    #[must_use]
    pub fn is_sat(&self) -> bool {
        matches!(self, Self::Optimal { .. } | Self::Feasible { .. })
    }

    /// True for `Infeasible`.
    #[must_use]
    pub fn is_infeasible(&self) -> bool {
        matches!(self, Self::Infeasible { .. })
    }

    /// True for `Unknown`.
    #[must_use]
    pub fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown { .. })
    }
}

#[cfg(test)]
mod trust_tests {
    use super::*;
    use crate::model::Model;
    use num_traits::Zero;

    fn integral() -> Model {
        let mut m = Model::new();
        m.add_int_col(0.0, 1.0);
        m
    }

    fn continuous() -> Model {
        let mut m = Model::new();
        m.add_col(0.0, 1.0);
        m
    }

    fn point() -> Vec<BigRational> {
        vec![BigRational::zero()]
    }

    /// THE ONE THAT MATTERS. `wishlist:152` justifies tolerating economics-only
    /// settings with "every verdict still rests on ay's exact certificates and
    /// `check_point` (fail-closed), so the recipe can change speed, never an
    /// answer". On an INTEGRAL model that is false even with a certificate present:
    /// `LpSession::verify` asserts `bound == value` only when
    /// `!model.has_integrality()`, so what the certificate proves there is
    /// non-crossing, and the integrality gap is closed by the search.
    ///
    /// Every one of the 133 instances in the development design notes carries `ints > 0`,
    /// so all 276 OPTIMAL verdicts in that dataset land on this arm.
    #[test]
    fn optimal_with_a_certificate_is_not_rim_closed_on_an_integral_model() {
        // A certificate object; its CONTENT is irrelevant here, because `trust`
        // reports what the verify path CHECKS, not whether this instance verifies.
        let cert = crate::cert::OptimalityCertificate {
            sense: crate::model::Sense::Minimize,
            objective: Vec::new(),
            bound: BigRational::zero(),
            multipliers: Vec::new(),
        };
        let with_cert = |c| Outcome::Optimal {
            value: BigRational::zero(),
            model_values: point(),
            cert: c,
        };

        // Same outcome, two models differing ONLY in integrality.
        assert!(
            with_cert(Some(cert.clone()))
                .trust(&continuous())
                .is_rim_closed(),
            "a continuous model DOES assert bound == value, so it closes"
        );
        assert!(
            !with_cert(Some(cert)).trust(&integral()).is_rim_closed(),
            "on an integral model the certificate is only checked for non-crossing, \
             so optimality is not rim-closed -- this is the sentence at wishlist:152 \
             failing on the shape the downstream optimization consumer's own workload produces"
        );

        // And without a certificate neither model closes.
        assert!(!with_cert(None).trust(&continuous()).is_rim_closed());
        assert!(!with_cert(None).trust(&integral()).is_rim_closed());
    }

    /// `Feasible` asserts a point exists, and `check_point` re-derives exactly
    /// that against the caller's model — so the bare form is rim-closed. Attaching
    /// the interrupted tree's dual bound adds a claim that is NOT independently
    /// checkable, and the outcome's own doc comment says so.
    #[test]
    fn a_dual_bound_downgrades_an_otherwise_rim_closed_feasible() {
        let m = integral();
        let bare = Outcome::Feasible {
            model_values: point(),
            incumbent_only: true,
            dual_bound: None,
        };
        assert!(bare.trust(&m).is_rim_closed());

        let bounded = Outcome::Feasible {
            model_values: point(),
            incumbent_only: true,
            dual_bound: Some(BigRational::zero()),
        };
        assert!(
            !bounded.trust(&m).is_rim_closed(),
            "the tree's weakest open bound is not independently checkable"
        );
    }

    /// Infeasibility is the shape where the rim really does close: either a Farkas
    /// witness or a whole-tree certificate re-derived in the caller's frame.
    #[test]
    fn infeasible_is_rim_closed_exactly_when_it_carries_evidence() {
        let m = integral();
        assert!(
            !Outcome::Infeasible {
                cert: None,
                tree_cert: None,
            }
            .trust(&m)
            .is_rim_closed(),
            "no witness, no closure"
        );
    }

    /// The SECOND EXIT. `LpSession::rigorous_bound` constructs this inline from
    /// `ns_bound` and never calls `finish`, so it never passes through the
    /// certificate policy — and its output feeds `narrow_col_bounds`, which
    /// TIGHTENS the model. Rigorous is not the same as exported.
    #[test]
    fn a_rigorous_bound_is_sound_but_not_rim_closed() {
        let m = integral();
        for rigorous in [true, false] {
            let o = Outcome::Bound {
                dual_bound: BigRational::zero(),
                rigorous,
            };
            assert!(
                !o.trust(&m).is_rim_closed(),
                "Bound{{rigorous:{rigorous}}} carries no exported artifact"
            );
        }
    }

    /// `Unknown` makes no claim, but `RimClosed` would read as an endorsement of
    /// one. Every `SearchTrusted` must say which claim is unbacked.
    #[test]
    fn every_search_trusted_answer_names_its_claim() {
        let m = integral();
        for o in [
            Outcome::Unknown {
                reason: UnknownReason::Timeout,
            },
            Outcome::Unbounded,
            Outcome::Optimal {
                value: BigRational::zero(),
                model_values: point(),
                cert: None,
            },
        ] {
            match o.trust(&m) {
                Trust::RimClosed => panic!("{o:?} must not claim rim closure"),
                Trust::SearchTrusted { why } => {
                    assert!(!why.trim().is_empty(), "{o:?} gave an empty reason");
                }
            }
        }
    }
}
