// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Unified result type for all CHC engines.
//!
//! All CHC solving engines (PDR, BMC, TPA, IMC, Kind, PDKind, TRL, CEGAR,
//! Decomposition) return `ChcEngineResult`. This eliminates 9 per-engine
//! result enums that previously duplicated the same Safe/Unsafe/Unknown
//! variants. Part of #2791.

use crate::pdr::counterexample::{Counterexample, CounterexampleStep};
use crate::pdr::model::{InvariantModel, PredicateInterpretation};
use crate::{ChcExpr, ChcProblem, ChcVar, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;

/// Unified result from any CHC solving engine.
#[derive(Debug, Clone)]
#[non_exhaustive]
#[must_use = "solver results must be checked — ignoring Safe/Unsafe loses correctness"]
pub enum ChcEngineResult {
    /// Safe: the system satisfies its specification.
    /// Contains an inductive invariant model (may be empty if the engine
    /// proves safety without producing an explicit invariant, e.g. TRL).
    Safe(InvariantModel),
    /// Unsafe: the system violates its specification.
    /// Contains a counterexample trace.
    Unsafe(Counterexample),
    /// Unknown: the engine could not determine the result within its budget.
    Unknown,
    /// Not applicable: the engine cannot handle this problem class
    /// (e.g., IMC/Kind on multi-predicate problems, Decomposition on
    /// non-decomposable problems).
    NotApplicable,
}

impl std::fmt::Display for ChcEngineResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Safe(model) => {
                write!(f, "safe (invariant with {} predicates)", model.len())
            }
            Self::Unsafe(cex) => {
                write!(f, "unsafe (counterexample at depth {})", cex.steps.len())
            }
            Self::Unknown => write!(f, "unknown"),
            Self::NotApplicable => write!(f, "not applicable"),
        }
    }
}

/// An invariant model that has been validated by the portfolio.
///
/// Private inner field ensures callers outside ay-chc cannot construct
/// verified invariants directly — they must come through the portfolio's
/// validation pipeline. Within ay-chc, the `pub(crate)` constructor
/// restricts creation to validated code paths.
///
/// Part of #5746: structural verification invariant Phase 2.
#[derive(Debug, Clone)]
#[must_use = "verified invariants should not be discarded"]
pub struct VerifiedInvariant {
    model: InvariantModel,
}

impl VerifiedInvariant {
    /// Wrap a validated invariant model.
    ///
    /// Only callable within ay-chc. All callers MUST verify the model
    /// through the portfolio's validation pipeline before calling this.
    pub(crate) fn from_validated(model: InvariantModel) -> Self {
        Self { model }
    }

    /// Get the underlying invariant model.
    pub fn model(&self) -> &InvariantModel {
        &self.model
    }

    /// Consume the wrapper and return the underlying `InvariantModel`.
    ///
    /// **Trust boundary:** The returned `InvariantModel` carries no compile-time
    /// proof of verification. Verification happened at construction time (via
    /// the portfolio's validation pipeline). Prefer using [`.model()`](Self::model)
    /// to borrow the inner model without stripping the verification wrapper.
    pub fn into_inner(self) -> InvariantModel {
        self.model
    }
}

/// A counterexample that has been validated by the portfolio.
///
/// Private inner field ensures callers outside ay-chc cannot construct
/// verified counterexamples directly — they must come through the portfolio's
/// validation pipeline (validate_unsafe → verify_counterexample).
///
/// Part of #5750: structural verification invariant Phase 5.
#[derive(Debug, Clone)]
#[must_use = "verified counterexamples should not be discarded"]
pub struct VerifiedCounterexample {
    cex: Counterexample,
}

impl VerifiedCounterexample {
    /// Wrap a validated counterexample.
    ///
    /// Only callable within ay-chc. All callers MUST verify the counterexample
    /// through verify_counterexample() before calling this.
    pub(crate) fn from_validated(cex: Counterexample) -> Self {
        Self { cex }
    }

    /// Get the underlying counterexample.
    pub fn counterexample(&self) -> &Counterexample {
        &self.cex
    }

    /// Consume the wrapper and return the underlying `Counterexample`.
    ///
    /// **Trust boundary:** The returned `Counterexample` carries no compile-time
    /// proof of verification. Verification happened at construction time (via
    /// `verify_counterexample()`). Prefer using
    /// [`.counterexample()`](Self::counterexample) to borrow without stripping
    /// the verification wrapper.
    pub fn into_inner(self) -> Counterexample {
        self.cex
    }
}

/// Marker proving `Unknown` was produced by the verification pipeline.
///
/// Cannot be constructed outside ay-chc — the private field prevents external
/// code from writing `VerifiedChcResult::Unknown(VerifiedUnknownMarker(...))`.
/// This closes the last external-construction bypass on `VerifiedChcResult`:
/// `Safe` and `Unsafe` are already protected by `VerifiedInvariant` and
/// `VerifiedCounterexample` having private fields.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum VerifiedUnknownReason {
    /// Generic solver inconclusive result. Covers budget exhaustion,
    /// cancellation, or an engine being unable to finish its proof search.
    Inconclusive,
    /// BMC completed its bounded search up to `max_depth` without finding
    /// a counterexample. This is useful for proof cross-checking but is NOT
    /// a safety proof.
    BmcExhaustedSearch,
    /// BMC stopped before reaching `max_depth` because its time budget ran out.
    BmcBudgetExhausted,
    /// The selected solving path could not handle this problem class.
    NotApplicable,
}

impl VerifiedUnknownReason {
    /// Stable snake_case machine code for evidence and routing consumers.
    pub fn code(&self) -> &'static str {
        match self {
            Self::Inconclusive => "inconclusive",
            Self::BmcExhaustedSearch => "bmc_exhausted_search",
            Self::BmcBudgetExhausted => "bmc_budget_exhausted",
            Self::NotApplicable => "not_applicable",
        }
    }

    /// Short human-readable label for the stable machine [`code`](Self::code).
    pub fn name(&self) -> &'static str {
        match self {
            Self::Inconclusive => "Inconclusive",
            Self::BmcExhaustedSearch => "BMC exhausted search",
            Self::BmcBudgetExhausted => "BMC budget exhausted",
            Self::NotApplicable => "Not applicable",
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct VerifiedUnknownMetadata {
    reason: VerifiedUnknownReason,
    bmc_max_depth: Option<usize>,
    bmc_depth_reached: Option<usize>,
}

#[derive(Debug, Clone)]
pub struct VerifiedUnknownMarker(pub(crate) VerifiedUnknownMetadata);

impl std::fmt::Display for VerifiedUnknownMarker {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.reason() {
            VerifiedUnknownReason::Inconclusive => write!(f, "unknown (inconclusive)"),
            VerifiedUnknownReason::BmcExhaustedSearch => {
                if let Some(max_depth) = self.bmc_max_depth() {
                    write!(
                        f,
                        "unknown (BMC searched to max_depth={} without finding a counterexample; \
                         not a safety proof)",
                        max_depth
                    )
                } else {
                    write!(
                        f,
                        "unknown (BMC exhausted its bounded search without finding a \
                         counterexample; not a safety proof)"
                    )
                }
            }
            VerifiedUnknownReason::BmcBudgetExhausted => {
                match (self.bmc_depth_reached(), self.bmc_max_depth()) {
                    (Some(depth_reached), Some(max_depth)) => write!(
                        f,
                        "unknown (BMC hit its time budget after depth {} of {}; \
                         cross-check inconclusive)",
                        depth_reached, max_depth
                    ),
                    _ => write!(
                        f,
                        "unknown (BMC hit its time budget before completing the bounded \
                         search)"
                    ),
                }
            }
            VerifiedUnknownReason::NotApplicable => {
                write!(f, "unknown (not applicable for this problem class)")
            }
        }
    }
}

impl VerifiedUnknownMarker {
    pub(crate) fn new() -> Self {
        Self(VerifiedUnknownMetadata {
            reason: VerifiedUnknownReason::Inconclusive,
            bmc_max_depth: None,
            bmc_depth_reached: None,
        })
    }

    pub(crate) fn not_applicable() -> Self {
        Self(VerifiedUnknownMetadata {
            reason: VerifiedUnknownReason::NotApplicable,
            bmc_max_depth: None,
            bmc_depth_reached: None,
        })
    }

    pub(crate) fn bmc_exhausted_search(max_depth: usize) -> Self {
        Self(VerifiedUnknownMetadata {
            reason: VerifiedUnknownReason::BmcExhaustedSearch,
            bmc_max_depth: Some(max_depth),
            bmc_depth_reached: Some(max_depth),
        })
    }

    pub(crate) fn bmc_budget_exhausted(depth_reached: usize, max_depth: usize) -> Self {
        Self(VerifiedUnknownMetadata {
            reason: VerifiedUnknownReason::BmcBudgetExhausted,
            bmc_max_depth: Some(max_depth),
            bmc_depth_reached: Some(depth_reached),
        })
    }

    /// Returns the structured reason carried by this verified `Unknown`.
    pub fn reason(&self) -> VerifiedUnknownReason {
        self.0.reason
    }

    /// Returns the configured BMC `max_depth` when this `Unknown` came from a
    /// BMC-only cross-check path.
    pub fn bmc_max_depth(&self) -> Option<usize> {
        self.0.bmc_max_depth
    }

    /// Returns the deepest BMC level reached before the run became inconclusive.
    pub fn bmc_depth_reached(&self) -> Option<usize> {
        self.0.bmc_depth_reached
    }
}

/// CHC result where Safe invariants and Unsafe counterexamples have been
/// validated by the portfolio.
///
/// This is the public return type of the portfolio solver. External callers
/// receive `VerifiedChcResult` instead of raw `ChcEngineResult`, ensuring
/// both Safe results and Unsafe counterexamples have passed validation.
///
/// All three variants are construction-sealed: external code cannot create
/// any variant without going through the verification pipeline.
/// - `Safe`: requires `VerifiedInvariant` (private field)
/// - `Unsafe`: requires `VerifiedCounterexample` (private field)
/// - `Unknown`: requires `VerifiedUnknownMarker` (private field)
///
/// Part of #5746 + #5750: structural verification invariant Phases 2 + 5.
#[derive(Debug, Clone)]
#[non_exhaustive]
#[must_use = "solver results must be checked — ignoring Safe/Unsafe loses correctness"]
pub enum VerifiedChcResult {
    /// Safe: the system satisfies its specification.
    /// The invariant has been validated by the portfolio.
    Safe(VerifiedInvariant),
    /// Unsafe: the system violates its specification.
    /// The counterexample has been validated by the portfolio.
    Unsafe(VerifiedCounterexample),
    /// Unknown: the solver could not determine the result within its budget.
    /// The marker ensures this variant was produced by the verification pipeline.
    Unknown(VerifiedUnknownMarker),
}

impl std::fmt::Display for VerifiedChcResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Safe(inv) => {
                write!(
                    f,
                    "safe (verified invariant with {} predicates)",
                    inv.model().len()
                )
            }
            Self::Unsafe(cex) => {
                write!(
                    f,
                    "unsafe (verified counterexample at depth {})",
                    cex.counterexample().steps.len()
                )
            }
            Self::Unknown(marker) => write!(f, "{marker}"),
        }
    }
}

/// Evidence of how a ChcEngineResult was validated before promotion to
/// VerifiedChcResult.
///
/// Every path from ChcEngineResult to VerifiedChcResult MUST supply evidence.
/// This makes the validation claim auditable: grep for `ValidationEvidence::`
/// construction sites to find every path that produces verified results.
///
/// Part of #5746: structural verification invariant Phase 2.
#[derive(Debug, Clone)]
pub(crate) enum ValidationEvidence {
    /// Full verification: init + transition + query clauses checked with a
    /// fresh verifier and standard budget.
    /// Used by: portfolio full validation and adaptive direct Safe validation.
    FullVerification,

    /// Counterexample validated via fresh PDR verification.
    /// Used by: AdaptivePortfolio::finalize_verified_result() before exposing
    /// VerifiedChcResult::Unsafe from the public verified API.
    CounterexampleVerification,

    /// Trivial problem: no predicate occurrences in clause bodies.
    /// All query constraints checked for satisfiability via direct SMT.
    /// No loop invariant needed — the problem has no loops.
    /// Used by: AdaptivePortfolio::solve_entry_exit_only()
    TrivialProblem,

    /// Algebraic synthesis proved safe with a closed-form recurrence model.
    /// Used by: AdaptivePortfolio::solve_internal() algebraic prepass.
    AlgebraicClosedForm,

    /// Catamorphism-abstraction SAT certificate (CHC-COMP agenda #7, CATA v1).
    ///
    /// Produced ONLY by `AdaptivePortfolio::try_cata_abstraction_route` after
    /// BOTH halves of its composite certification succeeded fail-closed:
    /// 1. every per-original-clause implication obligation `θ ⇒ θ#` was
    ///    discharged `unsat` by a fresh ADT+LIA+UF SMT query
    ///    (`CataAbstraction::discharge_obligations`), and
    /// 2. the abstract LIA model was fully re-verified against every abstract
    ///    clause with a fresh verifier
    ///    (`engines::validate_external_invariant_model`).
    /// Together these certify — on the ORIGINAL clauses — that composing the
    /// abstract model with the catamorphism definitions is an inductive
    /// invariant (abstract SAT ⇒ original SAT). The composed model itself
    /// materializes catamorphism values as reserved uninterpreted-function
    /// terms, which downstream UF-based re-checks treat conservatively.
    CataAbstraction {
        /// Catamorphism pool size at the accepting refinement level.
        /// Certificate provenance; read by `adaptive_cata_tests` assertions.
        #[allow(dead_code)]
        pool_size: usize,
        /// Number of per-clause implication obligations discharged.
        /// Certificate provenance; read by `adaptive_cata_tests` assertions.
        #[allow(dead_code)]
        obligations_discharged: usize,
    },

    /// BMC counterexample: the bounded model checker found a satisfying
    /// assignment to the reachability encoding (init ∧ trans^k ∧ query).
    /// This is source evidence only; the final verified-result boundary still
    /// replays the trace against the original CHC before exposing Unsafe.
    /// Used by: solve_complex_loop BMC probe, portfolio BMC engine
    BmcCounterexample,

    /// Exhaustive BMC proof for a scalar-only acyclic predicate DAG.
    ///
    /// This evidence is admissible for Bool/Int/BV scalar predicate state when
    /// the BMC engine exhaustively enumerated the acyclic predicate DAG. #9227
    /// showed that accepting the same empty-model proof shape for heap-liveness
    /// or array encodings is unsound, so array/datatype/real predicate state
    /// still requires a recheckable invariant model.
    ScalarAcyclicBmcExhaustive { max_depth: usize },

    /// Exact preprocessing inlined all predicates and every resulting
    /// query-only body was independently UNSAT in the transformed theory.
    ///
    /// This is stronger than an empty-model acyclic BMC result: no invariant is
    /// being inferred from bounded search. The transformed CHC has no predicate
    /// state left, and satisfiability of each bad-state body was discharged
    /// directly under an exact preprocessing pipeline.
    #[allow(dead_code)]
    PreprocessedQueryOnlyDischarge { query_count: usize },

    /// Double-run query-only discharge on an ORIGINALLY ACYCLIC problem
    /// (item 4 Stage 0 acceptance fix).
    ///
    /// Exact preprocessing inlined every predicate, every collapsed query body
    /// was proved UNSAT, and — after the translated empty Safe model failed
    /// per-rule validation on the original clauses (the model carries no
    /// reconstructible interpretations, which is a witness-completeness gap,
    /// not a soundness gap) — an INDEPENDENT fresh-executor run re-proved
    /// every collapsed query body UNSAT a second time. Two independent
    /// executor runs agreeing is the same trust baseline as any AY unsat.
    /// The original problem is acyclic, so the collapsed query bodies cover
    /// every derivation path exactly (no bounded-search under-approximation).
    ///
    /// Distinct from [`Self::PreprocessedQueryOnlyDischarge`] (single-run,
    /// rejected fail-closed at both promotion boundaries): this variant is
    /// only constructed by
    /// `AdaptivePortfolio::run_preprocessed_acyclic_bmc_probe` after the
    /// fresh-executor recheck confirmed, and both promotion boundaries gate
    /// it on the original problem being acyclic.
    CheckedQueryOnlyDischarge { query_count: usize },

    /// #9227 re-keyed empty-model acyclic BMC exhaustion for array-sorted
    /// ORIGINAL problems whose TRANSFORMED problem is array- and
    /// datatype-free under an equisat-grade transform chain
    /// (item 4 Stage 0 acceptance fix).
    ///
    /// The default #9227 stance (empty-model Safe + original arrays -> reject)
    /// keys the rejection on the ORIGINAL signature. This variant is only
    /// constructed when ALL of: (a) the transformed problem has no array and
    /// no datatype sorts, (b) every transform in the chain is equisat-grade
    /// ([`crate::transform::TransformMemoryReport::is_equisat_grade`],
    /// allowlisted equivalence-preserving passes only, fail-closed on unknown
    /// obligations), and (c) an independent fresh-executor BMC re-run of the
    /// same exhaustion query confirmed the empty-model Safe. Routed through
    /// its own variant (not `ScalarAcyclicBmcExhaustive`) so the finalize
    /// boundary can keep demoting every OTHER array-original empty-model
    /// Safe fail-closed.
    EquisatAcyclicBmcExhaustive {
        /// Exhausted acyclic depth (certificate provenance, mirrors
        /// `ScalarAcyclicBmcExhaustive`; surfaced via `Debug` logging only).
        #[allow(dead_code)]
        max_depth: usize,
    },

    /// FORALL-ARR ghost-pair lane (agenda #16): the Safe verdict is backed by
    /// a sealed `GhostPairCertificate` — a quantified array invariant that was
    /// fully discharged per-rule on the ORIGINAL clauses at construction time
    /// (instantiation-based, with a full quantified SMT fallback) and is
    /// re-checked at the finalize boundary. The carried model's
    /// quantifier-free interpretations are intentionally empty; the
    /// certificate is the witness.
    /// Used by: AdaptivePortfolio::try_array_ghost_pair_route().
    QuantifiedArrayInvariantCertificate,

    /// BMC-only API completed its bounded search without a counterexample.
    /// Used by: AdaptivePortfolio::solve_bmc_only_internal() when BMC reaches
    /// the configured depth bound.
    BmcExhaustedSearch { max_depth: usize },

    /// BMC-only API stopped because its time budget ran out before the
    /// configured depth bound.
    /// Used by: AdaptivePortfolio::solve_bmc_only_internal() when BMC reports
    /// budget exhaustion.
    BmcBudgetExhausted {
        depth_reached: usize,
        max_depth: usize,
    },
}

impl VerifiedChcResult {
    /// Promote a validated engine result to a verified result.
    ///
    /// Caller MUST supply evidence of what validation was performed.
    /// Replaces the old `from_validated_engine_result` (no evidence) to make
    /// every verification path auditable. Part of #5746.
    pub(crate) fn from_validated(result: ChcEngineResult, evidence: ValidationEvidence) -> Self {
        tracing::debug!(
            "Promoting to VerifiedChcResult with evidence: {:?}",
            evidence
        );
        match result {
            ChcEngineResult::Safe(model) => match evidence {
                ValidationEvidence::BmcExhaustedSearch { max_depth } => {
                    tracing::warn!(
                        max_depth,
                        model_predicates = model.len(),
                        "rejecting Safe result paired with BMC-exhaustion evidence (#9227)"
                    );
                    Self::Unknown(VerifiedUnknownMarker::bmc_exhausted_search(max_depth))
                }
                ValidationEvidence::BmcBudgetExhausted {
                    depth_reached,
                    max_depth,
                } => {
                    tracing::warn!(
                        depth_reached,
                        max_depth,
                        model_predicates = model.len(),
                        "rejecting Safe result paired with BMC-budget evidence (#9227)"
                    );
                    Self::Unknown(VerifiedUnknownMarker::bmc_budget_exhausted(
                        depth_reached,
                        max_depth,
                    ))
                }
                ValidationEvidence::PreprocessedQueryOnlyDischarge { query_count } => {
                    tracing::warn!(
                        query_count,
                        model_predicates = model.len(),
                        "rejecting Safe result paired with unvalidated preprocessed query-only \
                         discharge evidence"
                    );
                    Self::Unknown(VerifiedUnknownMarker::new())
                }
                // Explicit accept (item 4 Stage 0): the DOUBLE-RUN discharge
                // variant is only constructed after an independent
                // fresh-executor re-proof of every collapsed query body on an
                // originally acyclic problem — two independent executor runs
                // agreeing, the same trust baseline as any AY unsat. The
                // single-run `PreprocessedQueryOnlyDischarge` reject arm
                // above stays fail-closed.
                ValidationEvidence::CheckedQueryOnlyDischarge { query_count } => {
                    tracing::debug!(
                        query_count,
                        model_predicates = model.len(),
                        "accepting Safe backed by double-run checked query-only discharge"
                    );
                    Self::Safe(VerifiedInvariant::from_validated(model))
                }
                _ => Self::Safe(VerifiedInvariant::from_validated(model)),
            },
            ChcEngineResult::Unsafe(cex) => {
                Self::Unsafe(VerifiedCounterexample::from_validated(cex))
            }
            ChcEngineResult::Unknown => Self::Unknown(match evidence {
                ValidationEvidence::BmcExhaustedSearch { max_depth } => {
                    VerifiedUnknownMarker::bmc_exhausted_search(max_depth)
                }
                ValidationEvidence::BmcBudgetExhausted {
                    depth_reached,
                    max_depth,
                } => VerifiedUnknownMarker::bmc_budget_exhausted(depth_reached, max_depth),
                _ => VerifiedUnknownMarker::new(),
            }),
            ChcEngineResult::NotApplicable => {
                Self::Unknown(VerifiedUnknownMarker::not_applicable())
            }
        }
    }

    /// Returns `true` if the result is `Safe`.
    #[inline]
    pub fn is_safe(&self) -> bool {
        matches!(self, Self::Safe(_))
    }

    /// Returns `true` if the result is `Unsafe`.
    #[inline]
    pub fn is_unsafe(&self) -> bool {
        matches!(self, Self::Unsafe(_))
    }

    /// Returns `true` if the result is `Unknown`.
    #[inline]
    pub fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown(_))
    }

    /// Returns the verified unknown marker, if present.
    #[inline]
    pub fn unknown_marker(&self) -> Option<&VerifiedUnknownMarker> {
        match self {
            Self::Unknown(marker) => Some(marker),
            _ => None,
        }
    }

    /// Returns the structured reason for `Unknown`, if present.
    #[inline]
    pub fn unknown_reason(&self) -> Option<VerifiedUnknownReason> {
        self.unknown_marker().map(VerifiedUnknownMarker::reason)
    }

    /// Get the verified invariant if the result is `Safe`.
    #[inline]
    pub fn safe_invariant(&self) -> Option<&VerifiedInvariant> {
        match self {
            Self::Safe(inv) => Some(inv),
            _ => None,
        }
    }

    /// Get the verified counterexample if the result is `Unsafe`.
    #[inline]
    pub fn unsafe_counterexample(&self) -> Option<&VerifiedCounterexample> {
        match self {
            Self::Unsafe(cex) => Some(cex),
            _ => None,
        }
    }
}

/// Build an `InvariantModel` for a single-predicate problem from a `ChcExpr` invariant.
///
/// Handles the variable renaming from engine-internal `v0, v1, ...` format to
/// the canonical PDR format `__p{pred_index}_a{arg_index}`. Returns `None` if
/// the problem has no predicates or if variable counts don't match.
pub(crate) fn build_single_pred_model(
    problem: &ChcProblem,
    invariant: ChcExpr,
) -> Option<InvariantModel> {
    let pred = problem.predicates().first()?.clone();

    let engine_vars: Vec<_> = pred
        .arg_sorts
        .iter()
        .enumerate()
        .map(|(i, sort)| ChcVar::new(format!("v{i}"), sort.clone()))
        .collect();
    let pdr_vars: Vec<_> = pred
        .arg_sorts
        .iter()
        .enumerate()
        .map(|(i, sort)| ChcVar::new(format!("__p{}_a{i}", pred.id.index()), sort.clone()))
        .collect();

    if engine_vars.len() != pdr_vars.len() {
        return None;
    }

    let subst: Vec<_> = engine_vars
        .into_iter()
        .zip(pdr_vars.iter().cloned().map(ChcExpr::var))
        .collect();
    let formula = invariant.substitute(&subst);

    let mut model = InvariantModel::new();
    model.set(pred.id, PredicateInterpretation::new(pdr_vars, formula));
    Some(model)
}

/// Build a skeleton counterexample with `depth + 1` steps and no assignments.
///
/// Used by engines that prove unsafety but don't produce detailed traces
/// (IMC, Kind, PDKind).
pub(crate) fn skeleton_counterexample(problem: &ChcProblem, depth: usize) -> Counterexample {
    let pred = problem
        .predicates()
        .first()
        .map_or(PredicateId::new(0), |p| p.id);
    let steps = (0..=depth)
        .map(|_| CounterexampleStep::new(pred, FxHashMap::default()))
        .collect();
    Counterexample {
        steps,
        witness: None,
        ground_derivation: None,
    }
}

#[cfg(test)]
mod tests {
    use super::{
        ChcEngineResult, InvariantModel, ValidationEvidence, VerifiedChcResult,
        VerifiedUnknownReason,
    };

    #[test]
    fn verified_unknown_reason_code_and_name_are_stable_consumer_values() {
        let cases = [
            (
                VerifiedUnknownReason::Inconclusive,
                "inconclusive",
                "Inconclusive",
            ),
            (
                VerifiedUnknownReason::BmcExhaustedSearch,
                "bmc_exhausted_search",
                "BMC exhausted search",
            ),
            (
                VerifiedUnknownReason::BmcBudgetExhausted,
                "bmc_budget_exhausted",
                "BMC budget exhausted",
            ),
            (
                VerifiedUnknownReason::NotApplicable,
                "not_applicable",
                "Not applicable",
            ),
        ];

        for (reason, code, name) in cases {
            assert_eq!(reason.code(), code);
            assert_eq!(reason.name(), name);
        }
    }

    #[test]
    fn verified_unknown_reason_preserves_not_applicable() {
        let result = VerifiedChcResult::from_validated(
            ChcEngineResult::NotApplicable,
            ValidationEvidence::FullVerification,
        );

        assert!(result.is_unknown());
        assert_eq!(
            result.unknown_reason(),
            Some(VerifiedUnknownReason::NotApplicable)
        );
        assert_eq!(
            result.to_string(),
            "unknown (not applicable for this problem class)"
        );
    }

    #[test]
    fn verified_unknown_marker_tracks_bmc_bounded_search_metadata() {
        let result = VerifiedChcResult::from_validated(
            ChcEngineResult::Unknown,
            ValidationEvidence::BmcExhaustedSearch { max_depth: 17 },
        );
        let marker = result
            .unknown_marker()
            .expect("result should expose unknown marker");

        assert_eq!(
            result.unknown_reason(),
            Some(VerifiedUnknownReason::BmcExhaustedSearch)
        );
        assert_eq!(marker.bmc_max_depth(), Some(17));
        assert_eq!(marker.bmc_depth_reached(), Some(17));
        assert_eq!(
            result.to_string(),
            "unknown (BMC searched to max_depth=17 without finding a counterexample; not a safety proof)"
        );
    }

    #[test]
    fn safe_with_bmc_exhaustion_evidence_fails_closed() {
        let result = VerifiedChcResult::from_validated(
            ChcEngineResult::Safe(InvariantModel::new()),
            ValidationEvidence::BmcExhaustedSearch { max_depth: 3 },
        );

        assert!(result.is_unknown());
        assert_eq!(
            result.unknown_reason(),
            Some(VerifiedUnknownReason::BmcExhaustedSearch)
        );
    }
}
